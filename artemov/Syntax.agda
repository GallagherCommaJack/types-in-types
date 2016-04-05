module Syntax where
open import Data.Product
open import Data.Sum
open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Unit hiding (_≤_)
open import Function
open import Induction.WellFounded
open import Relation.Binary.PropositionalEquality

ᵏ : {A B : Set} → A → B → A
ᵏ a b = a

^ : ∀ {S : Set} {T : S → Set} {P : Σ S T → Set}
  → ((σ : Σ S T) → P σ)
  → (s : S) (t : T s) → P (s , t)
^ f s t = f (s , t)

infixr 5 _∶_

data Exp : ℕ → Set where
  &_ : ∀{n} → ℕ → Exp (suc n)
  ‘λ’_ : ∀{n} → Exp (suc n) → Exp (suc n)
  _◌_ : ∀{n} → Exp (suc n) → Exp (suc n) → Exp (suc n)
  exf : ∀{n} → Exp (suc n) → Exp 0 → Exp (suc n)
  _∶_ : ∀{n} → Exp (suc n) → Exp 0 → Exp 0
  _⊃_ : Exp 0 → Exp 0 → Exp 0
  ι : Exp 0

Tm : ℕ → Set
Tm n = Exp (suc n)

Ty : Set
Ty = Exp 0

!_ : ∀{n} → Tm n → Tm (suc n)
! (& x) = & x
! ‘λ’ t = ‘λ’ ! t
! (f ◌ x) = (! f) ◌ (! x)
! (exf f A) = exf (! f) A

¡_ : ∀{n} → Tm (suc n) → Tm n
¡ (& x) = & x
¡ (‘λ’ t) = ‘λ’ ¡ t
¡ (f ◌ x) = (¡ f) ◌ (¡ x)
¡ (exf f A) = exf (¡ f) A

¡! : ∀{n}(t : Tm n) → ¡ (! t) ≡ t
¡! (& x) = refl
¡! (‘λ’ t) = cong ‘λ’_ (¡! t)
¡! (f ◌ x) rewrite ¡! f | ¡! x = refl
¡! (exf f A) rewrite ¡! f = refl

!¡ : ∀{n}(t : Tm (suc n)) → ! (¡ t) ≡ t
!¡ (& x) = refl
!¡ (‘λ’ t) = cong ‘λ’_ (!¡ t)
!¡ (f ◌ x) rewrite !¡ f | !¡ x = refl
!¡ (exf f X) rewrite !¡ f = refl

Con = List Ty

data _∈_ {A : Set} (x : A) : List A → Set where
  top : ∀  {xs} → x ∈ (x ∷ xs)
  pop : ∀{y xs} → x ∈ xs → x ∈ (y ∷ xs)

mkIx : {A : Set} {Γ : List A} {a : A} → a ∈ Γ → ℕ
mkIx top = 0
mkIx (pop v) = suc (mkIx v)

data Thm (Γ : Con) : ℕ → Ty → Set
⌜_⌝ : ∀{Γ n}{A : Ty} → Thm Γ n A → Tm n

data Thm Γ where
  var : ∀{n}{A} → A ∈ Γ → Thm Γ n A
  lam : ∀{n}{A B : Ty} → Thm (A ∷ Γ) n B → Thm Γ n (A ⊃ B)
  app : ∀{n}{A B : Ty} → Thm Γ n (A ⊃ B) → Thm Γ n A → Thm Γ n B
  nec : ∀{n}{A : Ty} (d : Thm [] n A) → Thm Γ (suc n) (⌜ d ⌝ ∶ A)
  ref : ∀{n}{t : Tm n}{A : Ty} → Thm Γ (suc n) (t ∶ A) → Thm Γ n A
  exf : ∀{n} → Thm Γ n ι → ∀ A → Thm Γ n A

⌜ var x ⌝ = & (mkIx x)
⌜ lam d ⌝ = ‘λ’ ⌜ d ⌝
⌜ app f x ⌝ = ⌜ f ⌝ ◌ ⌜ x ⌝
⌜ nec d ⌝ = ! ⌜ d ⌝
⌜ ref d ⌝ = ¡ ⌜ d ⌝
⌜ exf f A ⌝ = exf ⌜ f ⌝ A

addstack : ∀{Γ n A} → Thm Γ n A → ∀ Δ → Thm (Γ ++ Δ) n A
addstack (var x) Δ = {!!}
addstack (lam d) Δ = {!!}
addstack (app d d₁) Δ = {!!}
addstack (nec d) Δ = nec d
addstack (ref d) Δ = {!!}
addstack (exf d A) Δ = {!!}
-- t : Tm 1
-- quine : Thm [] 2 ((‘λ’ (& 0)) ∶ (((‘λ’ (& 0)) ∶ ι) ⊃ ι))
-- isquine : ⌜ quine ⌝ ≡ ! t

-- t = ‘λ’ (& zero)
-- quine = nec (lam (ref (var top)))
-- isquine = refl

-- t : Tm 1
-- quine : ∀{Γ} → Thm Γ 1 ((t ∶ ι) ⊃ ι)
-- quineback : ∀{Γ} → Thm Γ 1 (ι ⊃ (t ∶ ι))
-- wrong1 : ∀{Γ} → Thm Γ 2 (t ∶ ι ⊃ (t ∶ ι))
-- false : Thm [] 1 ι

-- t = {!!}
-- quine = lam (ref (var top))
-- quineback = lam (exf (var top) (t ∶ ι))
-- wrong1 = nec (lam (exf (var top) (t ∶ ι)))
-- false = {!!}



-- ⟦_⟧ty : Ty → Set
-- ⟦ _∶_ {n} t A ⟧ty = Σ (Thm [] n A) (λ d → ⌜ d ⌝ ≡ t)
-- ⟦ A ⊃ B ⟧ty = ⟦ A ⟧ty → ⟦ B ⟧ty

-- ⟦_⟧c : Con → Set
-- ⟦ [] ⟧c = ⊤
-- ⟦ A ∷ Γ ⟧c = ⟦ Γ ⟧c × ⟦ A ⟧ty

-- thmsize : ∀{Γ n A} → Thm Γ n A → ℕ
-- thmsize (var x) = 1
-- thmsize (lam d) = suc (thmsize d)
-- thmsize (app f x) = suc (thmsize f + thmsize x)
-- thmsize (nec d) = suc (thmsize d)
-- thmsize (ref d) = suc (thmsize d)


-- _-_ : ℕ → ℕ → ℕ
-- n - zero = n
-- zero - _ = zero
-- suc n - suc m = n - m

-- measure : ∀{Γ n A} → Thm Γ n A → ℕ × ℕ
-- measure {Γ} {n} {A} d = n , thmsize d

-- _×<×_ = Lexicographic._<_

-- open import Relation.Binary
-- open import Induction.Nat
-- open import Level renaming (zero to lzero ; suc to lsuc)

-- _<l_ : Rel (ℕ × ℕ) _
-- _<l_ = _<′_ ×<× (λ _ → _<′_)

-- _≺_ : ∀{Γ n A Δ m B} → REL (Thm Γ n A) (Thm Δ m B) _
-- d1 ≺ d2 = measure d1 <l measure d2

-- data iAcc {A : Set} {B : A → Set} (R : ∀{a b} → REL (B a) (B b) lzero) (x : A) (b : B x) : Set where
--   iacc : (rs : ∀ y (c : B y) → R c b → iAcc (λ {a} {b} → R {a} {b}) y c) → iAcc R x b

-- Acc→iAcc : ∀{A : Set} {R : Rel A lzero} {x : A} → Acc {A = A} R x → iAcc {⊤} {λ _ → A} R tt x
-- Acc→iAcc (acc rs) = iacc (λ _ c cRx → Acc→iAcc (rs c cRx))

-- iAcc-inv : ∀{A : Set} { B : A → Set } {C R} {i : A} (f : {i : A} → B i → C ) x
--            → iAcc {⊤} {λ _ → C} R tt (f x)
--            → iAcc (λ {j} {k} a b → R (f {j} a) (f {k} b)) i x
-- iAcc-inv f x (iacc rs) = iacc (λ i c fcRfx → iAcc-inv f c (rs tt (f c) fcRfx))

-- Ders : Con × ℕ × Ty → Set
-- Ders (Γ , n , A) = Thm Γ n A

-- ⟦_⟧∈ : ∀{Γ A} → A ∈ Γ → ⟦ Γ ⟧c → ⟦ A ⟧ty
-- ⟦ top ⟧∈ = proj₂
-- ⟦ pop v ⟧∈ = ⟦ v ⟧∈ ∘ proj₁

-- open Lexicographic using (right ; left)

-- ⟦_⟧⊢ : ∀{Γ n A} → Thm Γ n A → ⟦ Γ ⟧c → ⟦ A ⟧ty
-- ⟦ d ⟧⊢ = Thm⇓ d {!!}
--   where Thm⇓ : ∀{Γ n A} (d : Thm Γ n A) → iAcc {B = Ders} _≺_ (Γ , n , A) d → ⟦ Γ ⟧c → ⟦ A ⟧ty
--         Thm⇓ (var x) wf γ = ⟦ x ⟧∈ γ
--         Thm⇓ (lam d) (iacc rs) γ a = Thm⇓ d (rs _ _ (right ≤′-refl)) (γ , a)
--         Thm⇓ (app f x) (iacc rs) γ = {!!}
--         Thm⇓ (nec d) wf γ = d , refl
--         Thm⇓ (ref d) (iacc rs) γ with Thm⇓ d (rs _ _ {!right!}) γ
--         ... | d⇓ , pd = {!!}
-- -- wf-iAcc : ∀{Γ n A} (d : Thm Γ n A) → iAcc {B = λ {(Δ , m , B) → Thm Δ m B}} _≺_ (Γ , n , A) d
-- -- wf-iAcc d = iacc (λ p c cRd → iAcc-inv measure c (Acc→iAcc {!!}))

-- --Thm⇓ : ∀{n A Γ} (d : Thm Γ n A) → ⟦ Γ ⟧c → ⟦ A ⟧ty
-- --Thm⇓ d wf γ = ?
-- -- data Tm (l : ℕ) : Set where
-- --   &_ : ℕ → Tm l
-- --   ‘λ’_ : Tm l → Tm l
-- --   _◌_ : Tm l → Tm l → Tm l

-- -- data Ty : ℕ → Set where
-- --   _∶_ : ∀{l} → Tm (suc l) → Ty l → Ty (suc l)
-- --   _⊃_ : ∀{n m} → Ty n → Ty m → Ty 0

-- -- !_ : ∀{n} → Tm n → Tm (suc n)
-- -- ! (& x) = & x
-- -- ! (‘λ’ t) = ‘λ’ ! t
-- -- ! (f ◌ x) = (! f) ◌ (! x)

-- -- Con = List (Σ ℕ Ty)

-- -- data _⊢_ (Γ : Con) : ∀{n} → Ty n → Set
-- -- ⌜_⌝ : ∀{Γ n}{T : Ty n} → Γ ⊢ T → Tm (suc n)

-- -- data _⊢_ Γ where
-- --   var : ∀{n A} → (n , A) ∈ Γ → Γ ⊢ A
-- --   lam : ∀{n}{A B : Ty n} → ((n , A) ∷ Γ) ⊢ B → Γ ⊢ (A ⊃ B)
-- --   app : ∀{n}{A B : Ty n} → Γ ⊢ (A ⊃ B) → Γ ⊢ A → Γ ⊢ B
-- --   nec : ∀{n}{A : Ty n} (d : [] ⊢ A) → Γ ⊢ (⌜ d ⌝ ∶ A)
-- --   ref : ∀{n t}{A : Ty n} → Γ ⊢ (t ∶ A) → Γ ⊢ A

-- -- ⌜ var x ⌝ = & (mkIx x)
-- -- ⌜ lam d ⌝ = {!⌜ d ⌝!}
-- -- ⌜ app f x ⌝ = {!!}
-- -- ⌜ nec d ⌝ = ! ⌜ d ⌝
-- -- ⌜ ref d ⌝ = ¡ ⌜ d ⌝

-- -- ⟦_⟧ty : ∀{n} → Ty n → Set
-- -- ⟦ t ∶ A ⟧ty = Σ ([] ⊢ A) (λ d → ⌜ d ⌝ ≡ t)
-- -- ⟦ A ⊃ B ⟧ty = ⟦ A ⟧ty → ⟦ B ⟧ty

-- -- listAll : ∀{A : Set} (P : A → Set) → List A → Set
-- -- listAll P [] = ⊤
-- -- listAll P (x ∷ xs) = listAll P xs × P x

-- -- ⟦_⟧c : Con → Set
-- -- ⟦_⟧c = listAll (⟦_⟧ty ∘ proj₂)

-- -- ⟦_⟧∈ : ∀{Γ T} → T ∈ Γ → ⟦ Γ ⟧c → ⟦ proj₂ T ⟧ty
-- -- ⟦ top ⟧∈   (γ , a) = a
-- -- ⟦ pop I ⟧∈ (γ , b) = ⟦ I ⟧∈ γ

-- -- Thm⇓ : ∀{Γ}{n}{A : Ty n} → Γ ⊢ A → ⟦ Γ ⟧c → ⟦ A ⟧ty
-- -- ⟦ var i ⟧⊢ = ⟦ i ⟧∈
-- -- ⟦ lam d ⟧⊢ = ^ ⟦ d ⟧⊢
-- -- ⟦ app f x ⟧⊢ = ⟦ f ⟧⊢ ˢ ⟦ x ⟧⊢
-- -- ⟦ nec d ⟧⊢ = λ _ → d , refl
-- -- ⟦ ref d ⟧⊢ γ with ⟦ d ⟧⊢ γ
-- -- ... | d¡ , pd = {!!}
-- -- -- Con = List Ty

-- -- -- lookup : {A : Set} (i : ℕ) (Γ : List A) → i < length Γ → A
-- -- -- lookup i [] ()
-- -- -- lookup zero (x ∷ Γ) (s≤s p) = x
-- -- -- lookup (suc i) (x ∷ Γ) (s≤s p) = lookup i Γ p

-- -- -- !_ : Tm → Tm
-- -- -- ! (λ^[ l ] t) = λ^[ suc l ] (! t)
-- -- -- ! (f ◌^[ l ] x) = (! f) ◌^[ suc l ] (! x)
-- -- -- ! (&^[ l ] i) = &^[ suc l ] i
-- -- -- --! (ref t) = t

-- -- -- data _⊢_ (Γ : Con) : Ty → Set
-- -- -- ⌜_⌝ : ∀{Γ T} → Γ ⊢ T → Tm

-- -- -- data _⊢_ Γ where
-- -- --   var : ∀{A} → A ∈ Γ → Γ ⊢ A
-- -- --   lam : ∀{A B} → (A ∷ Γ) ⊢ B → Γ ⊢ A ⊃ B
-- -- --   _◌_ : ∀{A B} → Γ ⊢ A ⊃ B → Γ ⊢ A → Γ ⊢ B
-- -- --   int : ∀{A} (D : [] ⊢ A) → Γ ⊢ ⌜ D ⌝ ∶ A
-- -- --   ref : ∀{A t} → Γ ⊢ t ∶ A → Γ ⊢ A
-- -- -- --  add : ∀{Δ t A} (p : Γ ⊢ (Γ ⊨ t ∶ A)) →  Γ ⊢ (Γ ⊨ ⌜ p ⌝ ∶ (Δ ⊨ t ∶ A))

-- -- -- ⌜ var v ⌝ = &^[ 0 ] (mkIx v)
-- -- -- ⌜ lam typ ⌝ = λ^[ 0 ] ⌜ typ ⌝
-- -- -- ⌜ f ◌ x ⌝ = ⌜ f ⌝ ◌^[ 0 ] ⌜ x ⌝
-- -- -- ⌜ int t ⌝ = ! ⌜ t ⌝
-- -- -- ⌜ ref d ⌝ = {!!}

-- -- -- refintinv : ∀{Γ t A}(d : [] ⊢ t ∶ A) → ⌜ int {Γ} (ref d) ⌝ ≡ ⌜ d ⌝
-- -- -- refintinv d = {!!}

-- -- -- -- tmsize : Tm → ℕ
-- -- -- -- tmsize (&^[ _ ] _) = 1
-- -- -- -- tmsize (λ^[ _ ] t) = suc (tmsize t)
-- -- -- -- tmsize (f ◌^[ _ ] x) = suc (tmsize f + tmsize x)
-- -- -- -- tmsize (ref t) = suc (tmsize t)

-- -- -- -- tysize : Ty → ℕ
-- -- -- -- tysize (x ∶ a) = suc (tmsize x + tysize a)
-- -- -- -- tysize (a ⊃ b) = suc (tysize a + tysize b)

-- -- -- -- --⌜ add t ⌝ = ! ⌜ t ⌝

-- -- -- -- ⟦_⟧ty : Ty → Set
-- -- -- -- ⟦ t ∶ A ⟧ty = Σ ([] ⊢ A) λ d → ⌜ d ⌝ ≡ t
-- -- -- -- ⟦ A ⊃ B ⟧ty = ⟦ A ⟧ty → ⟦ B ⟧ty

-- -- -- -- ⟦_⟧c : Con → Set
-- -- -- -- ⟦ [] ⟧c = ⊤
-- -- -- -- ⟦ A ∷ Γ ⟧c = ⟦ Γ ⟧c × ⟦ A ⟧ty

-- -- -- -- ⟦_⟧∈ : ∀{Γ T} → T ∈ Γ → ⟦ Γ ⟧c → ⟦ T ⟧ty
-- -- -- -- ⟦ top ⟧∈   (γ , a) = a
-- -- -- -- ⟦ pop I ⟧∈ (γ , b) = ⟦ I ⟧∈ γ

-- -- -- -- refCounter : ∀{Γ T} → Γ ⊢ T → ℕ
-- -- -- -- refCounter (var _) = 0
-- -- -- -- refCounter (lam d) = refCounter d
-- -- -- -- refCounter (f ◌ x) = refCounter f + refCounter x
-- -- -- -- refCounter (int d) = refCounter d
-- -- -- -- refCounter (ref d) = suc (refCounter d)

-- -- -- -- open import Level renaming (zero to lzero ; suc to lsuc)
-- -- -- -- open import Relation.Binary using ( Rel ; REL )
-- -- -- -- open import Induction.Nat

-- -- -- -- data iAcc {A : Set} {B : A → Set} (R : ∀{a b} → REL (B a) (B b) lzero) (x : A) (b : B x) : Set where
-- -- -- --   iacc : (rs : ∀ y (c : B y) → R c b → iAcc (λ {a} {b} → R {a} {b}) y c) → iAcc R x b

-- -- -- -- module Inverse-image-wf {A B : Set} {P : A → Set} (_<_ : B → B → Set) (f : {a : A} → P a → B) where
-- -- -- --   R : ∀{a b} → P a → P b → Set
-- -- -- --   R x y = f x < f y

-- -- -- --   ii-acc : ∀{a}{p : P a} → Acc _<_ (f p) → iAcc {A} {P} R a p
-- -- -- --   ii-acc {p = p} (acc rs) = iacc (λ y py py<p → ii-acc (rs (f py) py<p))

-- -- -- -- dsize : ∀{Γ T} → Γ ⊢ T → ℕ
-- -- -- -- dsize (var x) = 2
-- -- -- -- dsize (lam d) = suc (dsize d)
-- -- -- -- dsize (f ◌ x) = suc (dsize f + dsize x)
-- -- -- -- dsize (int d) = suc (dsize d)
-- -- -- -- dsize (ref {t = t} d) = suc (dsize d)

-- -- -- -- densizety : Ty → Set
-- -- -- -- densizety (_ ∶ _) = ℕ
-- -- -- -- densizety {A ⊃ B} = ⟦ A ⟧ty → densizety B

-- -- -- -- densize : ∀{T} → ⟦ T ⟧ty → densizety T
-- -- -- -- densize {x ∶ A} t = dsize (proj₁ t)
-- -- -- -- densize {A ⊃ B} t = λ a → densize (t a)

-- -- -- -- consize : ∀{Γ} → ⟦ Γ ⟧c → ℕ
-- -- -- -- consize {[]} _ = 1
-- -- -- -- consize {x ∷ Γ} (γ , x↓) = suc {!!}

-- -- -- -- thef : ∀{Γ A} → Γ ⊢ A → ℕ × ℕ
-- -- -- -- thef d = (tmsize ⌜ d ⌝ , dsize d)

-- -- -- -- open Inverse-image-wf {Con × Ty} {ℕ} {λ {(Γ , T) → Γ ⊢ T}} _<_ dsize renaming (R to _⋖_ ; ii-acc to ⋖-wf)
-- -- -- -- open import Relation.Binary

-- -- -- -- quoteSizeLem : ∀{Γ A}(d : Γ ⊢ A) → tmsize ⌜ d ⌝ < dsize d
-- -- -- -- quoteSizeLem (var x) = {!!} --s≤s (s≤s z≤n)
-- -- -- -- quoteSizeLem (lam d) = {!!} --s≤s (quoteSizeLem d)
-- -- -- -- quoteSizeLem (f ◌ x) = {!!}
-- -- -- -- quoteSizeLem (int d) = {!!}
-- -- -- -- quoteSizeLem (ref {t = t} d) = {!!} --s≤s (m≤m+n (tmsize t) (dsize d))

-- -- -- -- _≤-trans_ : ∀{x y z} → x ≤ y → y ≤ z → x ≤ z
-- -- -- -- p ≤-trans q = {!!}

-- -- -- -- Tm↓ : ∀{Γ A} (d : Γ ⊢ A) → iAcc {Con × Ty} {λ { (Γ , A) → Γ ⊢ A }} _⋖_ (Γ , A) d → ⟦ Γ ⟧c → ⟦ A ⟧ty
-- -- -- -- Tm↓ (var x) wf γ = ⟦ x ⟧∈ γ
-- -- -- -- Tm↓ (lam d) wf γ x = {!!}
-- -- -- -- Tm↓ (f ◌ x) wf γ = {!!}
-- -- -- -- Tm↓ (int d) wf γ = d , refl
-- -- -- -- Tm↓ (ref d) (iacc rs) γ with Tm↓ d (rs _ _ {!!}) γ
-- -- -- -- Tm↓ (ref {t = t} d) (iacc rs) γ | d↓ , pd = Tm↓ d↓ (rs _ d↓ {!!}) _

-- -- -- -- --<′-ℕ-wf : ∀ n → iAcc _<′_ tt n
-- -- -- -- --<′-ℕ-wf x = acc (λ _ → aux x)
-- -- -- -- --where aux : ∀ x y → y <′ x → iAcc _<′_ tt y
-- -- -- -- --aux .(suc y) y ≤′-refl = <′-ℕ-wf y
-- -- -- -- --aux ._ y (≤′-step y<x) = aux _ y y<x

-- -- -- -- -- open Lexicographic renaming ( _<_ to _lex_ ) renaming ( well-founded to wflex )
-- -- -- -- -- lllex : Rel (ℕ × ℕ) _
-- -- -- -- -- lllex = _<′_ lex (λ _ → _<′_)

-- -- -- -- -- wf-lllex : Well-founded lllex
-- -- -- -- -- wf-lllex = wflex _ _ <-well-founded <-well-founded

-- -- -- -- -- thef : ∀{Γ A} → Γ ⊢ A → ℕ × ℕ
-- -- -- -- -- thef d = refCounter d , dsize d

-- -- -- -- -- theF : Con × Ty → Set
-- -- -- -- -- theF ΓT = proj₁ ΓT ⊢ proj₂ ΓT

-- -- -- -- -- trel : ∀{ΓT₁ ΓT₂} → REL (theF ΓT₁) (theF ΓT₂) _
-- -- -- -- -- trel d₁ d₂ = lllex (thef d₁) (thef d₂)

-- -- -- -- -- Acc→iAcc : ∀{A : Set} {R : Rel A lzero} {x : A} → Acc {A = A} R x → iAcc {⊤} {λ _ → A} R tt x
-- -- -- -- -- Acc→iAcc (acc rs) = iacc (λ _ c cRx → Acc→iAcc (rs c cRx))

-- -- -- -- -- iAcc-inv : ∀{A : Set} { B : A → Set } {C R} {i : A} (f : {i : A} → B i → C ) x
-- -- -- -- --            → iAcc {⊤} {λ _ → C} R tt (f x)
-- -- -- -- --            → iAcc (λ {j} {k} a b → R (f {j} a) (f {k} b)) i x
-- -- -- -- -- iAcc-inv f x (iacc rs) = iacc (λ i c fcRfx → iAcc-inv f c (rs tt (f c) fcRfx))

-- -- -- -- -- wf-iAcc : ∀{Γ A} (d : Γ ⊢ A) → iAcc {B = theF} trel (Γ , A) d
-- -- -- -- -- wf-iAcc d = iacc (λ p c cRd → iAcc-inv thef c (Acc→iAcc (wf-lllex (thef c))))

-- -- -- -- -- -- open Inverse-image {_<_ = lllex} (λ d → refCounter d , dsize d) renaming ( well-founded to wfinv )

-- -- -- -- -- -- open Inverse-image-wf {Con × Ty} {ℕ} {λ { (Γ , A) → Γ ⊢ A }} lllex test

-- -- -- -- -- -- ⟦_⟧t : ∀{Γ A} → Γ ⊢ A → ⟦ Γ ⟧c → ⟦ A ⟧ty
-- -- -- -- -- -- ⟦_⟧t (var x) γ = ⟦ x ⟧∈ γ
-- -- -- -- -- -- ⟦_⟧t (lam d) γ = λ a → ⟦ d ⟧t (γ , a)
-- -- -- -- -- -- ⟦_⟧t (f ◌ x) γ = ⟦ f ⟧t γ (⟦ x ⟧t γ)
-- -- -- -- -- -- ⟦_⟧t (int d) γ = d
-- -- -- -- -- -- ⟦_⟧t (ref d) γ = ⟦ ⟦ d ⟧t γ ⟧t _

-- -- -- -- -- fapp-trel : ∀{Γ A B}(f : Γ ⊢ A ⊃ B)(x : Γ ⊢ A) → trel f (f ◌ x)
-- -- -- -- -- fapp-trel f x rewrite +-comm (refCounter f) (refCounter x) with refCounter x
-- -- -- -- -- ... | zero = right (s≤′s (m≤′m+n (dsize f) (dsize x)))
-- -- -- -- -- ... | suc rx = left (s≤′s (n≤′m+n rx (refCounter f)))

-- -- -- -- -- xapp-trel : ∀{Γ A B}(f : Γ ⊢ A ⊃ B)(x : Γ ⊢ A) → trel x (f ◌ x)
-- -- -- -- -- xapp-trel f x with refCounter f
-- -- -- -- -- xapp-trel f x | zero = right (s≤′s (n≤′m+n (dsize f) (dsize x)))
-- -- -- -- -- xapp-trel f x | suc rx = left (s≤′s (n≤′m+n rx (refCounter x)))

-- -- -- -- -- ⟦_⟧tt : ∀{Γ A} → (d : Γ ⊢ A) → iAcc {B = theF} trel (Γ , A) d → ⟦ Γ ⟧c → ⟦ A ⟧ty
-- -- -- -- -- ⟦_⟧tt (var x) wf γ = ⟦ x ⟧∈ γ
-- -- -- -- -- ⟦_⟧tt (lam d) (iacc rs) γ = λ a → ⟦ d ⟧tt (rs _ d (right ≤′-refl)) (γ , a)
-- -- -- -- -- ⟦_⟧tt (f ◌ x) (iacc rs) γ = ⟦ f ⟧tt (rs _ f (fapp-trel f x)) γ (⟦ x ⟧tt (rs _ x (xapp-trel f x)) γ)
-- -- -- -- -- ⟦_⟧tt (int d) wf γ = d
-- -- -- -- -- ⟦_⟧tt (ref d) (iacc rs) γ = ⟦ ⟦ d ⟧tt (rs _ d {!!}) γ ⟧tt (rs _ {!!} {!!}) _

-- -- -- -- -- -- -- Tm↓ : ∀{Γ A} (d : Γ ⊢ A) → Acc {Con × Ty} {λ { (Γ , A) → Γ ⊢ A }} R (Γ , A) d → ⟦ Γ ⟧c → ⟦ A ⟧ty
-- -- -- -- -- -- -- Tm↓Lem : ∀{Γ A t} (d : Γ ⊢ t ∶ A) (wf : Acc R (Γ , t ∶ A) d) (γ : ⟦ Γ ⟧c) → dsize (Tm↓ d wf γ) ≤′ dsize d

-- -- -- -- -- -- -- Tm↓ (var I) wf = ⟦ I ⟧∈
-- -- -- -- -- -- -- Tm↓ (lam D) (acc rs) γ a = Tm↓ D (rs _ D ≤′-refl) (γ , a)
-- -- -- -- -- -- -- Tm↓ (F ◌ X) (acc rs) γ = Tm↓ F (rs _ F (s≤′s (m≤′m+n (dsize F) (dsize X)))) γ (Tm↓ X (rs _ X (s≤′s (n≤′m+n (dsize F) (dsize X)))) γ)
-- -- -- -- -- -- -- Tm↓ (int D) wf γ = D
-- -- -- -- -- -- -- Tm↓ {Γ} (ref D) (acc rs) γ = Tm↓ (Tm↓ D (rs _ D ≤′-refl) γ) (rs _ (Tm↓ D (rs _ D ≤′-refl) γ) (s≤′s (Tm↓Lem _ (rs _ D ≤′-refl) γ))) _

-- -- -- -- -- -- -- Tm↓Lem (var x) (acc rs) γ = {!!}
-- -- -- -- -- -- -- Tm↓Lem (f ◌ x) wf γ = {!!}
-- -- -- -- -- -- -- Tm↓Lem (int d) wf γ = ≤′-step ≤′-refl
-- -- -- -- -- -- -- Tm↓Lem (ref d) (acc rs) γ = {!!}
-- -- -- -- -- -- -- --⟦ add t ⟧⊢ γ = t

-- -- -- -- -- -- -- --¡ : ∀{Γ t u A} → Γ ⊢ t ∶ u ∶ A → Γ ⊢ 
-- -- -- -- -- -- -- -- data _⊢_∋₁_ (Γ : Con) : Ty → ⊢ → Set where
-- -- -- -- -- -- -- --   var : ∀ i (p : i < length Γ) → Γ ⊢ lookup i Γ p ∋ (& i)
-- -- -- -- -- -- -- --   lam : ∀ A b → λ^[ 0 ] 
