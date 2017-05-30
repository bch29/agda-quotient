module Quotient.Inferable where

open import Quotient.Basic
open import Quotient.Setoid using (Setoid)


record Of {c p} (S : Setoid c p) : Set c where
  constructor of

  field
    value : Setoid.Of S

open Of public

record _≈_ {c p} {S : Setoid c p} (x y : Of S) : Set p where
  constructor lift≈

  field
    lower≈ : Setoid._[_≈_] S (value x) (value y)

open _≈_ public


refl : ∀ {c p} {S : Setoid c p} {x : Of S} → x ≈ x
refl {S = S} = lift≈ (Setoid.refl S)

sym : ∀ {c p} {S : Setoid c p} {x y : Of S} → x ≈ y → y ≈ x
sym {S = S} eq = lift≈ (Setoid.sym S (lower≈ eq))

trans : ∀ {c p} {S : Setoid c p} {x y z : Of S} → x ≈ y → y ≈ z → x ≈ z
trans {S = S} e1 e2 = lift≈ (Setoid.trans S (lower≈ e1) (lower≈ e2))

infixl 0 begin_
infixr 1 _≈⟨_⟩_ _≡⟨⟩_
infixl 2 _∎

data Chain {c p} {S : Setoid c p} : Of S → Of S → Set (c ⊔ p) where
  _≈⟨_⟩_ : ∀ x {y z} → x ≈ y → Chain y z → Chain x z
  _∎ : ∀ x → Chain x x

_≡⟨⟩_ : ∀ {c p} {S : Setoid c p} (x : Of S) {y} → Chain x y → Chain x y
_≡⟨⟩_ x = x ≈⟨ refl ⟩_

begin_ : ∀ {c p} {S : Setoid c p} {x y : Of S} → Chain x y → x ≈ y
begin (x ≈⟨ eq ⟩ chain) = trans eq (begin chain)
begin (x ∎) = refl
