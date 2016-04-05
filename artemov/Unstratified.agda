module Unstratified where
open import Data.Product
open import Data.Sum
open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Unit
open import Function
open import Induction.WellFounded
open import Relation.Binary.PropositionalEquality

ᵏ : {A B : Set} → A → B → A
ᵏ a b = a

^ : ∀ {S : Set} {T : S → Set} {P : Σ S T → Set}
  → ((σ : Σ S T) → P σ)
  → (s : S) (t : T s) → P (s , t)
^ f s t = f (s , t)

data Tm : Set where
  &^[_]_ : ℕ → ℕ → Tm
  λ^[_]_ : ℕ → Tm → Tm
  _◌^[_]_ : Tm → ℕ → Tm → Tm --application
  --!_  : Tm → Tm

infixr 5 _∶_

data Ty : Set where
  _∶_ : Tm → Ty → Ty
  _⊃_ : Ty → Ty → Ty

data _∈_ {A : Set} (x : A) : List A → Set where
  top : ∀  {xs} → x ∈ (x ∷ xs)
  pop : ∀{y xs} → x ∈ xs → x ∈ (y ∷ xs)

Con = List Ty

lookup : {A : Set} (i : ℕ) (Γ : List A) → i < length Γ → A
lookup i [] ()
lookup zero (x ∷ Γ) (s≤s p) = x
lookup (suc i) (x ∷ Γ) (s≤s p) = lookup i Γ p

!_ : Tm → Tm
! (λ^[ l ] t) = λ^[ suc l ] (! t)
! (f ◌^[ l ] x) = (! f) ◌^[ suc l ] (! x)
! (&^[ l ] i) = &^[ suc l ] i

mkIx : {A : Set} {Γ : List A} {a : A} → a ∈ Γ → ℕ
mkIx top = 0
mkIx (pop v) = suc (mkIx v)

infixr 0 _⊢_
data _⊢_ (Γ : Con) : Ty → Set
⌜_⌝ : ∀{Γ T} → Γ ⊢ T → Tm

data _⊢_ Γ where
  var : ∀{A} → A ∈ Γ → Γ ⊢ A
  lam : ∀{A B} → (A ∷ Γ) ⊢ B → Γ ⊢ A ⊃ B
  _◌_ : ∀{A B} → Γ ⊢ A ⊃ B → Γ ⊢ A → Γ ⊢ B
  int : ∀{A} (D : [] ⊢ A) → Γ ⊢ ⌜ D ⌝ ∶ A
  ref : ∀{A t} → Γ ⊢ t ∶ A → Γ ⊢ A
--  add : ∀{Δ t A} (p : Γ ⊢ (Γ ⊨ t ∶ A)) →  Γ ⊢ (Γ ⊨ ⌜ p ⌝ ∶ (Δ ⊨ t ∶ A))

⌜ var v ⌝ = &^[ 0 ] (mkIx v)
⌜ lam typ ⌝ = λ^[ 0 ] ⌜ typ ⌝
⌜ f ◌ x ⌝ = ⌜ f ⌝ ◌^[ 0 ] ⌜ x ⌝
⌜ int t ⌝ = ! ⌜ t ⌝
⌜ ref t ⌝ = ⌜ t ⌝

tmsize : Tm → ℕ
tmsize (&^[ _ ] _) = 1
tmsize (λ^[ _ ] t) = suc (tmsize t)
tmsize (f ◌^[ _ ] x) = suc (tmsize f + tmsize x)

tysize : Ty → ℕ
tysize (x ∶ a) = suc (tmsize x + tysize a)
tysize (a ⊃ b) = suc (tysize a + tysize b)

dsize : ∀{Γ T} → Γ ⊢ T → ℕ
dsize (var x) = 1
dsize (lam d) = suc (dsize d)
dsize (f ◌ x) = suc (dsize f + dsize x)
dsize (int d) = suc (dsize d)
dsize (ref d) = suc (dsize d)

--⌜ add t ⌝ = ! ⌜ t ⌝

⟦_⟧ty : Ty → Set
⟦ t ∶ A ⟧ty = [] ⊢ A
⟦ A ⊃ B ⟧ty = ⟦ A ⟧ty → ⟦ B ⟧ty

⟦_⟧c : Con → Set
⟦ [] ⟧c = ⊤
⟦ A ∷ Γ ⟧c = ⟦ Γ ⟧c × ⟦ A ⟧ty

⟦_⟧∈ : ∀{Γ T} → T ∈ Γ → ⟦ Γ ⟧c → ⟦ T ⟧ty
⟦ top ⟧∈   (γ , a) = a
⟦ pop I ⟧∈ (γ , b) = ⟦ I ⟧∈ γ

refCounter : ∀{Γ T} → Γ ⊢ T → ℕ
refCounter (var _) = 0
refCounter (lam d) = refCounter d
refCounter (f ◌ x) = refCounter f + refCounter x
refCounter (int d) = refCounter d
refCounter (ref d) = suc (refCounter d)

open import Level renaming (zero to lzero ; suc to lsuc)
open import Relation.Binary using ( Rel ; REL )
data iAcc {A : Set} {B : A → Set} (R : ∀{a b} → REL (B a) (B b) lzero) (x : A) (b : B x) : Set where
  iacc : (rs : ∀ y (c : B y) → R c b → iAcc (λ {a} {b} → R {a} {b}) y c) → iAcc R x b

--module Inverse-image-wf {A B : Set} {P : A → Set} (_<_ : B → B → Set) (f : {a : A} → P a → B) where
--R : ∀{a b} → P a → P b → Set
--R x y = f x < f y
--
--ii-acc : ∀{a}{p : P a} → iAcc _<_ tt (f p) → iAcc {A} {P} R a p
--ii-acc {p = p} (iacc rs) = acc (λ y py py<p → ii-acc (rs _ (f py) py<p))
--
--<′-ℕ-wf : ∀ n → iAcc _<′_ tt n
--<′-ℕ-wf x = acc (λ _ → aux x)
--where aux : ∀ x y → y <′ x → iAcc _<′_ tt y
--aux .(suc y) y ≤′-refl = <′-ℕ-wf y
--aux ._ y (≤′-step y<x) = aux _ y y<x

open Lexicographic renaming ( _<_ to _lex_ ) renaming ( well-founded to wflex )
lllex : Rel (ℕ × ℕ) _
lllex = _<′_ lex (λ _ → _<′_)

open import Induction.Nat
wf-lllex : Well-founded lllex
wf-lllex = wflex _ _ <-well-founded <-well-founded

thef : ∀{Γ A} → Γ ⊢ A → ℕ × ℕ
thef d = refCounter d , dsize d

theF : Con × Ty → Set
theF ΓT = proj₁ ΓT ⊢ proj₂ ΓT

trel : ∀{ΓT₁ ΓT₂} → REL (theF ΓT₁) (theF ΓT₂) _
trel d₁ d₂ = lllex (thef d₁) (thef d₂)

Acc→iAcc : ∀{A : Set} {R : Rel A lzero} {x : A} → Acc {A = A} R x → iAcc {⊤} {λ _ → A} R tt x
Acc→iAcc (acc rs) = iacc (λ _ c cRx → Acc→iAcc (rs c cRx))

iAcc-inv : ∀{A : Set} { B : A → Set } {C R} {i : A} (f : {i : A} → B i → C ) x
           → iAcc {⊤} {λ _ → C} R tt (f x)
           → iAcc (λ {j} {k} a b → R (f {j} a) (f {k} b)) i x
iAcc-inv f x (iacc rs) = iacc (λ i c fcRfx → iAcc-inv f c (rs tt (f c) fcRfx))

wf-iAcc : ∀{Γ A} (d : Γ ⊢ A) → iAcc {B = theF} trel (Γ , A) d
wf-iAcc d = iacc (λ p c cRd → iAcc-inv thef c (Acc→iAcc (wf-lllex (thef c))))

-- open Inverse-image {_<_ = lllex} (λ d → refCounter d , dsize d) renaming ( well-founded to wfinv )

-- open Inverse-image-wf {Con × Ty} {ℕ} {λ { (Γ , A) → Γ ⊢ A }} lllex test

-- ⟦_⟧t : ∀{Γ A} → Γ ⊢ A → ⟦ Γ ⟧c → ⟦ A ⟧ty
-- ⟦_⟧t (var x) γ = ⟦ x ⟧∈ γ
-- ⟦_⟧t (lam d) γ = λ a → ⟦ d ⟧t (γ , a)
-- ⟦_⟧t (f ◌ x) γ = ⟦ f ⟧t γ (⟦ x ⟧t γ)
-- ⟦_⟧t (int d) γ = d
-- ⟦_⟧t (ref d) γ = ⟦ ⟦ d ⟧t γ ⟧t _

fapp-trel : ∀{Γ A B}(f : Γ ⊢ A ⊃ B)(x : Γ ⊢ A) → trel f (f ◌ x)
fapp-trel f x rewrite +-comm (refCounter f) (refCounter x) with refCounter x
... | zero = right (s≤′s (m≤′m+n (dsize f) (dsize x)))
... | suc rx = left (s≤′s (n≤′m+n rx (refCounter f)))

xapp-trel : ∀{Γ A B}(f : Γ ⊢ A ⊃ B)(x : Γ ⊢ A) → trel x (f ◌ x)
xapp-trel f x with refCounter f
xapp-trel f x | zero = right (s≤′s (n≤′m+n (dsize f) (dsize x)))
xapp-trel f x | suc rx = left (s≤′s (n≤′m+n rx (refCounter x)))

⟦_⟧tt : ∀{Γ A} → (d : Γ ⊢ A) → iAcc {B = theF} trel (Γ , A) d → ⟦ Γ ⟧c → ⟦ A ⟧ty
⟦_⟧tt (var x) wf γ = ⟦ x ⟧∈ γ
⟦_⟧tt (lam d) (iacc rs) γ = λ a → ⟦ d ⟧tt (rs _ d (right ≤′-refl)) (γ , a)
⟦_⟧tt (f ◌ x) (iacc rs) γ = ⟦ f ⟧tt (rs _ f (fapp-trel f x)) γ (⟦ x ⟧tt (rs _ x (xapp-trel f x)) γ)
⟦_⟧tt (int d) wf γ = d
⟦_⟧tt (ref d) (iacc rs) γ = ⟦ ⟦ d ⟧tt (rs _ d {!!}) γ ⟧tt (rs _ {!!} {!!}) _

-- -- Tm↓ : ∀{Γ A} (d : Γ ⊢ A) → Acc {Con × Ty} {λ { (Γ , A) → Γ ⊢ A }} R (Γ , A) d → ⟦ Γ ⟧c → ⟦ A ⟧ty
-- -- Tm↓Lem : ∀{Γ A t} (d : Γ ⊢ t ∶ A) (wf : Acc R (Γ , t ∶ A) d) (γ : ⟦ Γ ⟧c) → dsize (Tm↓ d wf γ) ≤′ dsize d

-- -- Tm↓ (var I) wf = ⟦ I ⟧∈
-- -- Tm↓ (lam D) (acc rs) γ a = Tm↓ D (rs _ D ≤′-refl) (γ , a)
-- -- Tm↓ (F ◌ X) (acc rs) γ = Tm↓ F (rs _ F (s≤′s (m≤′m+n (dsize F) (dsize X)))) γ (Tm↓ X (rs _ X (s≤′s (n≤′m+n (dsize F) (dsize X)))) γ)
-- -- Tm↓ (int D) wf γ = D
-- -- Tm↓ {Γ} (ref D) (acc rs) γ = Tm↓ (Tm↓ D (rs _ D ≤′-refl) γ) (rs _ (Tm↓ D (rs _ D ≤′-refl) γ) (s≤′s (Tm↓Lem _ (rs _ D ≤′-refl) γ))) _

-- -- Tm↓Lem (var x) (acc rs) γ = {!!}
-- -- Tm↓Lem (f ◌ x) wf γ = {!!}
-- -- Tm↓Lem (int d) wf γ = ≤′-step ≤′-refl
-- -- Tm↓Lem (ref d) (acc rs) γ = {!!}
-- -- --⟦ add t ⟧⊢ γ = t

-- -- --⇓ : ∀{Γ t u A} → Γ ⊢ t ∶ u ∶ A → Γ ⊢ 
-- -- -- data _⊢_∋₁_ (Γ : Con) : Ty → ⊢ → Set where
-- -- --   var : ∀ i (p : i < length Γ) → Γ ⊢ lookup i Γ p ∋ (& i)
-- -- --   lam : ∀ A b → λ^[ 0 ] 
