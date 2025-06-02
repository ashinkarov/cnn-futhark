open import Data.Product
open import Data.Unit
open import Data.Empty
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin as F using (Fin; zero; suc)
open import Data.List as L using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Function

open import Ar
open import Lang
open import Real

module Eval (r : Real) where
  open Real.Real r

  ⟦_⟧ˢ : IS → Set
  ⟦ ix s ⟧ˢ = P s
  ⟦ ar s ⟧ˢ = Ar s R
  
  ⟦_⟧ᶜ : Ctx → Set
  ⟦ ε ⟧ᶜ = ⊤
  ⟦ Γ ▹ is ⟧ᶜ = ⟦ Γ ⟧ᶜ × ⟦ is ⟧ˢ
  
  lookup : is ∈ Γ → ⟦ Γ ⟧ᶜ → ⟦ is ⟧ˢ
  lookup v₀ (_ , x) = x
  lookup (there v) (ρ , _) = lookup v ρ

  zbs : (i j : P s) → (P s → R) → R
  zbs i j x with i ≟ₚ j
  ... | yes _ = x i
  ... | no _ = fromℕ 0


  zb : (i j : P s) → ⟦ ar p ⟧ˢ → ⟦ ar p ⟧ˢ
  zb i j x with i ≟ₚ j
  ... | yes _ = x
  ... | no _ = K (fromℕ 0)

  eval : E Γ is → ⟦ Γ ⟧ᶜ → ⟦ is ⟧ˢ
  eval (var x) ρ = lookup x ρ
  eval zero ρ = K (fromℕ 0)
  eval one ρ = K (fromℕ 1)
  eval (imaps e) ρ i = eval e (ρ , i) [] 
  eval (sels e e₁) ρ = K (eval e ρ (eval e₁ ρ))
  eval (imap e) ρ i = let i , j = splitP i in eval e (ρ , i) j
  eval (sel e e₁) ρ = nest (eval e ρ) (eval e₁ ρ)
  eval (E.imapb x e) ρ = Ar.imapb (λ i → eval e (ρ , i)) x
  eval (E.selb x e e₁) ρ = Ar.selb (eval e ρ) x (eval e₁ ρ)
  eval (E.sum e) ρ = Ar.sum (Ar.zipWith _+_) (Ar.K (fromℕ 0)) (λ i → eval e (ρ , i))
  eval (zero-but e e₁ e₂) ρ = zb (eval e ρ) (eval e₁ ρ) (eval e₂ ρ) 
  --with eval e ρ ≟ₚ eval e₁ ρ
  --... | yes _ = eval e₂ ρ
  --... | no  _ = Ar.K (fromℕ 0)
  eval (E.slide e x e₁ x₁) ρ = Ar.slide (eval e ρ) x (eval e₁ ρ) x₁
  eval (E.backslide e e₁ x x₁) ρ = Ar.backslide (eval e ρ) (eval e₁ ρ) x (fromℕ 0) x₁
  eval (logistic e) ρ = Ar.map logisticʳ (eval e ρ)
  eval (e ⊞ e₁) ρ = Ar.zipWith _+_ (eval e ρ) (eval e₁ ρ)
  eval (e ⊠ e₁) ρ = Ar.zipWith _*_ (eval e ρ) (eval e₁ ρ)
  eval (scaledown x e) ρ = Ar.map (_÷ fromℕ x) (eval e ρ) 
  eval (minus e) ρ = Ar.map -_ (eval e ρ)
  eval (let′ e e₁) ρ = eval e₁ (ρ , eval e ρ)

  _≈ᵃ_ : Ar s X → Ar s X → Set
  a ≈ᵃ b = ∀ i → a i ≡ b i

  _≈ˢ_ : (a b : ⟦ is ⟧ˢ) → Set
  _≈ˢ_ {ix s} a b = a ≡ b
  _≈ˢ_ {ar s} a b = a ≈ᵃ b

  _≈ᵉ_ : E Γ is → E Γ is → Set
  _≈ᵉ_ {Γ} a b = (ρ : ⟦ Γ ⟧ᶜ) → eval a ρ ≈ˢ eval b ρ

  reflᵉ : ∀ (e : E Γ is) → e ≈ᵉ e
  reflᵉ {is} {ix x} = λ e ρ → refl
  reflᵉ {is} {ar x} = λ e ρ i → refl

  reflˢ : ∀ {x : ⟦ is ⟧ˢ} → x ≈ˢ x 
  reflˢ {ix x₁}  = refl
  reflˢ {ar x₁} i = refl

  reflᵃ : ∀ {a : Ar s X} → a ≈ᵃ a
  reflᵃ i = refl

  infix 4 _∙ᵃ_
  _∙ᵃ_ : {a b c : Ar s X} → a ≈ᵃ b → b ≈ᵃ c → a ≈ᵃ c
  p ∙ᵃ q = λ i → p i ∙ q i  

  infix 4 _∙ˢ_
  _∙ˢ_ : {a b c : ⟦ is ⟧ˢ} → a ≈ˢ b → b ≈ˢ c → a ≈ˢ c
  _∙ˢ_ {ix x} p q = p ∙ q
  _∙ˢ_ {ar x} p q = p ∙ᵃ q

  data _≈ᶜ_ : ⟦ Γ ⟧ᶜ → ⟦ Γ ⟧ᶜ → Set where
    ε : tt ≈ᶜ tt
    _▹_ : ∀ {ρ ν : ⟦ Γ ⟧ᶜ} → ρ ≈ᶜ ν → ∀ {a b : ⟦ is ⟧ˢ} → a ≈ˢ b → (ρ , a) ≈ᶜ (ν , b)

  reflᶜ : ∀ {ρ : ⟦ Γ ⟧ᶜ} → ρ ≈ᶜ ρ
  reflᶜ {ε} = ε
  reflᶜ {Γ ▹ x} = reflᶜ ▹ reflˢ

  infixl 4 _∙ᶜ_
  _∙ᶜ_ : {a b c : ⟦ Γ ⟧ᶜ} → a ≈ᶜ b → b ≈ᶜ c → a ≈ᶜ c
  _∙ᶜ_ {ε} ε ε = ε
  _∙ᶜ_ {Γ ▹ x} (p ▹ x₁) (q ▹ x₂) = (p ∙ᶜ q) ▹ (x₁ ∙ˢ x₂)

  lookup-≈ᶜ : {ρ ν : ⟦ Γ ⟧ᶜ} → ρ ≈ᶜ ν → (v : is ∈ Γ) → lookup v ρ ≈ˢ lookup v ν
  lookup-≈ᶜ (eq ▹ x) v₀ = x
  lookup-≈ᶜ (eq ▹ x) (there v) = lookup-≈ᶜ eq v

  eval-cong : (e : E Γ is) {ρ ν : ⟦ Γ ⟧ᶜ} → ρ ≈ᶜ ν → eval e ρ ≈ˢ eval e ν
  eval-cong (var x) eq = lookup-≈ᶜ eq x
  eval-cong zero eq = λ i → refl
  eval-cong one eq = λ i → refl
  eval-cong (imaps e) eq i = eval-cong e (eq ▹ refl) []
  eval-cong (sels e e₁) eq i = eval-cong e eq (eval e₁ _) ∙ cong (eval e _) (eval-cong e₁ eq)
  eval-cong (imap e) eq i = eval-cong e (eq ▹ refl) (splitP i .proj₂)
  eval-cong (sel e e₁) eq i = eval-cong e eq (eval e₁ _ ++ i) ∙ cong (eval e _) (cong (_++ i) (eval-cong e₁ eq))
  eval-cong (E.imapb x e) eq i = eval-cong e (eq ▹ refl) (ix-mod i x)
  eval-cong (E.selb x e e₁) eq i = eval-cong e eq (ix-combine (eval e₁ _) i x)
                                   ∙ cong (eval e _) (cong (λ t → ix-combine t i x) (eval-cong e₁ eq))
  eval-cong (E.sum e) eq i = sum-inv _+_ (fromℕ 0) {λ i → eval e (_ , i)} i 
                             ∙ sum-cong _+_ (fromℕ 0) {(λ j → eval e (_ , j) i)} 
                                            (λ j → eval-cong e (eq ▹ refl) i)
                             ∙ sym (sum-inv _+_ (fromℕ 0) {λ i → eval e (_ , i)} i) 
  eval-cong (zero-but e e₁ e₂) {ρ}{ν} eq i with eval e ρ ≟ₚ eval e₁ ρ | eval e ν ≟ₚ eval e₁ ν
  ... | yes _ | yes _ = eval-cong e₂ eq i
  ... | yes p | no q  = ⊥-elim (q (sym (eval-cong e eq) ∙ p ∙ eval-cong e₁ eq))
  ... | no p  | yes q = ⊥-elim (p (eval-cong e eq ∙ q ∙ sym (eval-cong e₁ eq)))
  ... | no _  | no _  = refl
  eval-cong (E.slide e x e₁ x₁) eq i = eval-cong e₁ eq _ 
                                       ∙ cong (eval e₁ _) 
                                              (cong (λ t → (t ⊕′ i) x₁ x) (eval-cong e eq)) 
  eval-cong (E.backslide e e₁ x x₁) {ρ}{ν} eq i rewrite eval-cong e eq with (i ⊝′ eval e ν) x x₁
  ... | yes (k , p) = eval-cong e₁ eq k
  ... | no _ = refl
  eval-cong (logistic e) eq i = cong logisticʳ (eval-cong e eq i)
  eval-cong (e ⊞ e₁) eq i = cong₂ _+_ (eval-cong e eq i) (eval-cong e₁ eq i)
  eval-cong (e ⊠ e₁) eq i = cong₂ _*_ (eval-cong e eq i) (eval-cong e₁ eq i)
  eval-cong (scaledown x e) eq i = cong (_÷ fromℕ x) (eval-cong e eq i)
  eval-cong (minus e) eq i = cong (-_) (eval-cong e eq i)
  eval-cong (let′ e e₁) eq i = eval-cong e₁ (eq ▹ eval-cong e eq) i

  open WkSub hiding (_∙ˢ_)

  sub-env : Sub Γ Δ → ⟦ Γ ⟧ᶜ → ⟦ Δ ⟧ᶜ 
  sub-env ε ρ = tt
  sub-env (s ▹ x) ρ = sub-env s ρ , eval x ρ

  wk-env : (p : Γ ⊆ Δ) → ⟦ Δ ⟧ᶜ → ⟦ Γ ⟧ᶜ
  wk-env ε ρ = ρ
  wk-env (skip p) (ρ , _) = wk-env p ρ
  wk-env (keep p) (ρ , x) = wk-env p ρ , x

  wk-env-id : ∀ {ρ : ⟦ Γ ⟧ᶜ} → wk-env ⊆-eq ρ ≈ᶜ ρ
  wk-env-id {Γ = ε} = ε
  wk-env-id {Γ = Γ ▹ x} = wk-env-id ▹ reflˢ

  eval-wkv : (w : Γ ⊆ Δ) (v : is ∈ Γ) (ρ : ⟦ Δ ⟧ᶜ)
           → lookup (wkv w v) ρ ≈ˢ lookup v (wk-env w ρ)
  eval-wkv (skip w) v ρ = eval-wkv w v (ρ .proj₁)
  eval-wkv (keep w) v₀ ρ = reflˢ
  eval-wkv (keep w) (there v) ρ = eval-wkv w v (ρ .proj₁)

  eval-wk : (w : Γ ⊆ Δ) (e : E Γ is) (ρ : ⟦ Δ ⟧ᶜ)
          → eval (wk w e) ρ ≈ˢ eval e (wk-env w ρ)
  eval-wk w (var x) ρ = eval-wkv w x ρ
  eval-wk w zero ρ i = refl
  eval-wk w one ρ i = refl
  eval-wk w (imaps e) ρ i = eval-wk (keep w) e (ρ , i) []
  eval-wk w (sels e e₁) ρ i = cong (eval (wk w e) ρ) (eval-wk w e₁ ρ) 
                              ∙ eval-wk w e ρ (eval e₁ (wk-env w ρ))
  eval-wk w (imap e) ρ i = eval-wk (keep w) e (ρ , splitP i .proj₁) (splitP i .proj₂)
  eval-wk w (sel e e₁) ρ i = cong (λ t → eval (wk w e) ρ (t ++ i)) (eval-wk w e₁ ρ)
                             ∙ eval-wk w e ρ (eval e₁ (wk-env w ρ) ++ i)
  eval-wk w (E.imapb x e) ρ i = eval-wk (keep w) e (ρ , ix-div i x) (ix-mod i x)
  eval-wk w (E.selb x e e₁) ρ i = cong (λ t → eval (wk w e) ρ (ix-combine t i x)) (eval-wk w e₁ ρ)
                                  ∙ eval-wk w e ρ (ix-combine (eval e₁ (wk-env w ρ)) i x)
  eval-wk w (E.sum e) ρ i = sum-inv _+_ (fromℕ 0) {(λ i₁ → eval (wk (keep w) e) (ρ , i₁))} i
                            ∙ sum-cong _+_ (fromℕ 0) (λ t → eval-wk (keep w) e (ρ , t) i)
                            ∙ sym (sum-inv _+_ (fromℕ 0) {(λ i₁ → eval e (wk-env w ρ , i₁))} i)
  eval-wk w (zero-but e e₁ e₂) ρ with eval-wk w e ρ | eval-wk w e₁ ρ 
                                    | eval (wk w e) ρ ≟ₚ eval (wk w e₁) ρ
                                    | eval e (wk-env w ρ) ≟ₚ eval e₁ (wk-env w ρ)
  ... | p | q | yes r | no rr = ⊥-elim (rr (sym p ∙ r ∙ q))
  ... | p | q | yes r | yes rr = eval-wk w e₂ ρ
  ... | p | q | no r  | yes rr = ⊥-elim (r (p ∙ rr ∙ sym q))
  ... | p | q | no r  | no rr = λ i → refl
  eval-wk w (E.slide e x e₁ x₁) ρ = Ar.slide-cong (eval-wk w e ρ) x x₁ (eval-wk w e₁ ρ) 
  eval-wk w (E.backslide e e₁ x x₁) ρ = Ar.backslide-cong (eval-wk w e ρ) (eval-wk w e₁ ρ) x (fromℕ 0) x₁
  eval-wk w (logistic e) ρ = Ar.map-cong logisticʳ (eval-wk w e ρ)
  eval-wk w (e ⊞ e₁) ρ = zipWith-cong _+_ (eval-wk w e ρ) (eval-wk w e₁ ρ)
  eval-wk w (e ⊠ e₁) ρ = zipWith-cong _*_ (eval-wk w e ρ) (eval-wk w e₁ ρ)
  eval-wk w (scaledown x e) ρ = Ar.map-cong (_÷ fromℕ x) (eval-wk w e ρ) 
  eval-wk w (minus e) ρ = Ar.map-cong -_ (eval-wk w e ρ)
  eval-wk w (let′ e e₁) ρ = eval-cong (wk (keep w) e₁){ν = ρ , eval e (wk-env w ρ)} (reflᶜ ▹ eval-wk w e ρ) 
                            ∙ˢ eval-wk (keep w) e₁ _

  sub-env-wks : (s : Sub Γ Δ) → (w : Γ ⊆ Ψ) → ∀ ρ → sub-env (wks s w) ρ ≈ᶜ sub-env s (wk-env w ρ)
  sub-env-wks ε w _ = ε
  sub-env-wks (s ▹ x) w ρ = sub-env-wks s w ρ ▹ eval-wk w x ρ

  sub-env-cong : (s : Sub Γ Δ) → ∀ {ρ ν} → ρ ≈ᶜ ν → sub-env s ρ ≈ᶜ sub-env s ν 
  sub-env-cong ε p = ε
  sub-env-cong (s ▹ x) p = sub-env-cong s p ▹ eval-cong x p

  sub-env-sdrop : {ρ : ⟦ Δ ⟧ᶜ} {i : ⟦ is ⟧ˢ}(s : Sub Δ Γ) 
                → sub-env (sdrop s) (ρ , i) ≈ᶜ sub-env s ρ
  sub-env-sdrop ε = ε
  sub-env-sdrop {ρ = ρ}{i} (s ▹ x) 
    = sub-env-sdrop s 
      ▹ (eval-wk (skip ⊆-eq) x (ρ , i) ∙ˢ eval-cong x wk-env-id)
  
  sub-env-id : {ρ : ⟦ Γ ⟧ᶜ} → sub-env sub-id ρ ≈ᶜ ρ
  sub-env-id {Γ = ε} = ε
  sub-env-id {Γ = Γ ▹ x} = (sub-env-sdrop _ ∙ᶜ sub-env-id) ▹ reflˢ

  eval-subv : (s : Sub Δ Γ) (ρ : ⟦ Δ ⟧ᶜ) → (x : is ∈ Γ) → eval (subv s x) ρ ≈ˢ lookup x (sub-env s ρ)
  eval-subv (s ▹ x) ρ v₀ = reflˢ
  eval-subv (s ▹ _) ρ (there x) = eval-subv s ρ x

  eval-sub : (e : E Γ is) (ρ : ⟦ Δ ⟧ᶜ) (s : Sub Δ Γ) → eval (sub e s) ρ ≈ˢ eval e (sub-env s ρ)
  eval-sub (var x) ρ s = eval-subv s ρ x
  eval-sub zero ρ s = reflᵃ
  eval-sub one ρ s = reflᵃ
  eval-sub (imaps e) ρ s i = eval-sub e (ρ , i) (skeep s) [] 
                             ∙ eval-cong e (sub-env-sdrop _ ▹ refl) []
  eval-sub (sels e e₁) ρ s [] = eval-sub e ρ s (eval (sub e₁ s) ρ) 
                                ∙ cong (eval e (sub-env s ρ)) (eval-sub e₁ ρ s)
  eval-sub (imap {s = s} e) ρ su i with splitP {s = s} i
  ... | l , r = eval-sub e (ρ , l) _ r 
                ∙ eval-cong e ((sub-env-wks su (skip ⊆-eq)(ρ , l) 
                                ∙ᶜ sub-env-cong su wk-env-id) ▹ refl) r
  eval-sub (sel e e₁) ρ s i = eval-sub e ρ s (eval (sub e₁ s) ρ ++ i) 
                              ∙ cong (λ t → eval e (sub-env s ρ) (t ++ i)) (eval-sub e₁ ρ s)
  eval-sub (E.imapb x e) ρ s i = eval-sub e (ρ , ix-div i x) (wks s (skip ⊆-eq) ▹ var v₀) (ix-mod i x)
                                 ∙ eval-cong e ((sub-env-wks s (skip ⊆-eq) (ρ , ix-div i x) 
                                                 ∙ᶜ sub-env-cong s wk-env-id) ▹ refl) 
                                               (ix-mod i x)
  eval-sub (E.selb x e e₁) ρ s i = eval-sub e ρ s (ix-combine (eval (sub e₁ s) ρ) i x) 
                                   ∙ cong (eval e (sub-env s ρ))
                                          (cong (λ t → ix-combine t i x ) (eval-sub e₁ ρ s))
  eval-sub (E.sum e) ρ s i = sum-inv _+_ (fromℕ 0) {(λ i₁ → eval (sub e (wks s (skip ⊆-eq) ▹ var v₀)) (ρ , i₁))} i
                             ∙ sum-cong _+_ (fromℕ 0) 
                                            {(λ j → eval (sub e (wks s (skip ⊆-eq) ▹ var v₀)) (ρ , j) i)}
                                            (λ j → eval-sub e (ρ , j) ((wks s (skip ⊆-eq) ▹ var v₀)) i
                                                   ∙ eval-cong e ((sub-env-wks s (skip ⊆-eq) (ρ , j)
                                                                   ∙ᶜ sub-env-cong s wk-env-id) ▹ refl) i) 
                             ∙ sym (sum-inv _+_ (fromℕ 0){λ i₁ → eval e (sub-env s ρ , i₁)} i)
  eval-sub (zero-but e e₁ e₂) ρ s i with eval (sub e s) ρ ≟ₚ eval (sub e₁ s) ρ 
                                       | eval-sub e ρ s | eval-sub e₁ ρ s
  eval-sub (zero-but e e₁ e₂) ρ s i | no ¬p  | q | w rewrite q | w 
                                                    with eval e (sub-env s ρ) ≟ₚ eval e₁ (sub-env s ρ)
  ... | yes p = ⊥-elim (¬p p)
  ... | no _ = refl
  eval-sub (zero-but e e₁ e₂) ρ s i | yes a | q | w rewrite q | w
                                                    with eval e (sub-env s ρ) ≟ₚ eval e₁ (sub-env s ρ)
  ... | yes _ = eval-sub e₂ ρ s i
  ... | no ¬q = ⊥-elim (¬q a)
  eval-sub (E.slide e x e₁ x₁) ρ s i rewrite eval-sub e ρ s = eval-sub e₁ ρ s ((_ ⊕′ i) x₁ x)
  eval-sub (E.backslide e e₁ x x₁) ρ s i rewrite eval-sub e ρ s with (i ⊝′ eval e (sub-env s ρ)) x x₁
  ... | yes (k , p) = eval-sub e₁ ρ s k
  ... | no _ = refl
  eval-sub (logistic e) ρ s i = cong logisticʳ (eval-sub e ρ s i)
  eval-sub (e ⊞ e₁) ρ s i = cong₂ _+_ (eval-sub e ρ s i) (eval-sub e₁ ρ s i)
  eval-sub (e ⊠ e₁) ρ s i = cong₂ _*_ (eval-sub e ρ s i) (eval-sub e₁ ρ s i)
  eval-sub (scaledown x e) ρ s i = cong (_÷ fromℕ x) (eval-sub e ρ s i)
  eval-sub (minus e) ρ s i = cong -_ (eval-sub e ρ s i)
  eval-sub (let′ e e₁) ρ s i = eval-sub e₁ (ρ , eval (sub e s) ρ) ((wks s (skip ⊆-eq) ▹ var v₀)) i
                               ∙ eval-cong e₁ ((sub-env-wks s (skip ⊆-eq) (ρ , eval (sub e s) ρ)
                                                ∙ᶜ sub-env-cong s wk-env-id) ▹ eval-sub e ρ s) i

  eval-zb : (a : E Γ (ar s)) (i : E Γ (ix p)) → ∀ ρ → eval (zero-but i i a) ρ ≈ᵃ eval a ρ
  eval-zb a i ρ with eval i ρ ≟ₚ eval i ρ
  ... | yes refl = λ _ → refl
  ... | no ¬p = ⊥-elim (¬p refl)

  module ZeroBut (rp : RealProp r) where
    open RealProp rp

    zbs-suc-r : (i : P (n ∷ [])) (j : P (n ∷ [])) (is js : P s) (t : P (n ∷ s) → R)
              → zbs (j ++ js) (i ++ is) (t) ≡ zbs js is (λ ks → zbs (j) (i) (λ k → t (k ++ ks)))
    zbs-suc-r (i ∷ []) (j ∷ []) is js t with js ≟ₚ is | j F.≟ i | (j ∷ js) ≟ₚ (i ∷ is)
    ... | yes _ | yes refl | yes _ = refl
    ... | yes refl | yes refl | no ¬p = ⊥-elim (¬p refl)
    ... | yes _ | no _ | no _ = refl
    ... | yes _ | no ¬p | yes refl = ⊥-elim (¬p refl)
    ... | no _  | yes refl | no _ = refl
    ... | no ¬p  | yes refl | yes refl = ⊥-elim (¬p refl)
    ... | no _ | no _ | no _ = refl
    ... | no ¬p | no _ | yes refl = ⊥-elim (¬p refl)

    sum₁-zero : sum₁ {n = n} _+_ (fromℕ 0) (K (fromℕ 0)) ≡ fromℕ 0
    sum₁-zero {zero} = refl
    sum₁-zero {suc n} = +-neutˡ ∙ sum₁-zero {n}

    sum-zero : Ar.sum {s = s} _+_ (fromℕ 0) (λ _ → fromℕ 0) ≡ fromℕ 0
    sum-zero {s = []} = refl -- +-neutʳ
    sum-zero {s = x ∷ s} = sum₁-cong {n = x} _+_ (fromℕ 0) (λ i → sum-zero {s}) ∙ sum₁-zero {x}

    zbs-zero : (t : P (suc n ∷ []) → R) 
             → sum₁ _+_ (fromℕ 0) (λ x → zbs (zero ∷ []) (ιsuc x) t) ≡ fromℕ 0
    zbs-zero {n} t = sum₁-cong _+_ (fromℕ 0) {(λ x → zbs (zero ∷ []) (ιsuc x) t)} go ∙ sum₁-zero {n}
      where go : (i : _) → zbs (zero ∷ []) (ιsuc i) t ≡ fromℕ 0
            go (i ∷ []) = refl

    zbs-suc : (i j : P (n ∷ [])) (t : P (suc n ∷ []) → R)
            → zbs (ιsuc i) (ιsuc j) t ≡ zbs i j (t ∘ ιsuc)
    zbs-suc (i ∷ []) (j ∷ []) t with (i ∷ []) ≟ₚ (j ∷ []) | (suc i ∷ []) ≟ₚ (suc j ∷ [])
    ... | yes _ | yes _ = refl
    ... | yes refl | no ¬p = ⊥-elim (¬p refl)
    ... | no _ | no _ = refl
    ... | no ¬p | yes refl = ⊥-elim (¬p refl)

    zbs-sum₁-s : (j : P (n ∷ [])) (t : P (n ∷ []) → R)
              → Ar.sum₁ _+_ (fromℕ 0) (λ i → zbs j i t) ≡ t j
    zbs-sum₁-s (zero ∷ []) t rewrite zbs-zero t = +-neutʳ
    zbs-sum₁-s (suc j ∷ []) t = +-neutˡ 
                               ∙ sum₁-cong _+_ (fromℕ 0) {(λ x → zbs (suc j ∷ []) (ιsuc x) t)} 
                                               (λ i → zbs-suc (j ∷ []) i t)
                               ∙ zbs-sum₁-s (j ∷ []) (t ∘ ιsuc)

    zbs-sum-s : (j : P s) → (t : P s → R)
             → Ar.sum (_+_) (fromℕ 0) (λ i → zbs j i t) ≡ t j
    zbs-sum-s [] t = refl --+-neutˡ
    zbs-sum-s (px ∷ j) t = sum₁-cong _+_ (fromℕ 0) {(λ i → Ar.sum _+_ (fromℕ 0)
                                                          (λ j₁ → zbs (px ∷ j) (i ++ j₁) t ))} 
                                        (λ k → sum-cong _+_ (fromℕ 0) {(λ j₁ → zbs (px ∷ j) (k ++ j₁) t)} 
                                                            (λ ks → zbs-suc-r k (px ∷ []) ks j t)
                                               ∙ zbs-sum-s j (λ ks → zbs (px ∷ []) k (λ k₁ → t (k₁ ++ ks))))
                          ∙ zbs-sum₁-s (px ∷ []) (λ k₁ → t (k₁ ++ j))
                 --  
    zb-zbs : (i j : P s) (k : P p) (t : P s → P p → R)
           → zb i j (t j) k ≡ zbs i j (λ p → t p k)
    zb-zbs i j k t with i ≟ₚ j
    ... | yes refl = refl
    ... | no _ = refl

    zbs-sym : (i j : P s) (t : P s → R)
            → zbs i j t ≡ zbs j i t
    zbs-sym i j t with i ≟ₚ j | j ≟ₚ i
    ... | yes refl | yes refl = refl
    ... | yes refl | no ¬p = ⊥-elim (¬p refl)
    ... | no ¬p | yes refl = ⊥-elim (¬p refl)
    ... | no _ | no _ = refl

    zb-sym : (i j : P s) (k : P p) (t : P s → P p → R)
           → zb i j (t i) k ≡ zb j i (t i) k
    zb-sym i j k t with i ≟ₚ j | j ≟ₚ i
    ... | yes refl | yes refl = refl
    ... | yes refl | no ¬p = ⊥-elim (¬p refl)
    ... | no ¬p | yes refl = ⊥-elim (¬p refl)
    ... | no _ | no _ = refl

    zbs-cong : (f g : P s → R) → (∀ i → f i ≡ g i) 
             → (i j : P s) → zbs i j f ≡ zbs i j g 
    zbs-cong f g pf i j with i ≟ₚ j
    ... | yes _ = pf i
    ... | no _ = refl

    zb-sum : (j : P s) → (t : P s → Ar p R)
           → Ar.sum (Ar.zipWith _+_) (K (fromℕ 0)) (λ i → zb j i (t i)) ≈ᵃ t j
    zb-sum j t i = sum-inv _+_ (fromℕ 0) {(λ i → zb j i (t i))} i
                   ∙ sum-cong _+_ (fromℕ 0) {λ j₁ → (zb j j₁ (t j₁)) i} (λ j₁ → zb-zbs j j₁ i t)
                   ∙ zbs-sum-s j (λ k → t k i) 


    zbs-ext : (i j : P p) → (t : P s → R)
            → Ar.sum _+_ (fromℕ 0) (λ z → zbs i j (λ _ → t z)) ≡ zbs i j (λ _ → Ar.sum _+_ (fromℕ 0) t)
    zbs-ext {s = s} i j t with i ≟ₚ j
    ... | yes _ = refl
    ... | no _ = sum-zero {s}

    zb-zbs-k : (i j : P s) (k : P p) (t : P p → R)
               → zb i j t k ≡ zbs i j (λ _ → t k)
    zb-zbs-k i j k t with i ≟ₚ j
    ... | yes refl = refl
    ... | no _ = refl
