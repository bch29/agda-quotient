module Quotient.Setoid where

open import Quotient.Basic
open import Quotient.Setoid.Core public
open import Quotient.ISetoid.Core

import Relation.Binary.PropositionalEquality as PropEq

indexed : ∀ {ℓ c p} (I : Set ℓ) → Setoid c p → ISetoid I c p
indexed I S = record
  { Of↑ = λ _ → Of S
  ; _↑[_≈_] = S [_≈_]
  ; isEquivalence↑ = record
    { refl = refl S
    ; sym = sym S
    ; trans = trans S
    }
  }

Prop : ∀ {c} (A : Set c) → Setoid c c
Prop A = record
  { Of = A
  ; _[_≈_] = PropEq._≡_
  ; isEquivalence = PropEq.isEquivalence
  }

infixl 0 begin[_]_
infixr 1 _≈⟨_⟩_ _≡⟨⟩_ _≡⟨_⟩_
infixl 2 _∎

data Chain {c p} (S : Setoid c p) : Of S → Of S → Set (c ⊔ p) where
  _≈⟨_⟩_ : ∀ x {y z} → S [ x ≈ y ] → Chain S y z → Chain S x z
  _∎ : ∀ x → Chain S x x

_≡⟨⟩_ : ∀ {c p} {S : Setoid c p} x {y} → Chain S x y → Chain S x y
_≡⟨⟩_ {S = S} x = x ≈⟨ refl S ⟩_

_≡⟨_⟩_ : ∀ {c p} {S : Setoid c p} x {y z} → Prop (Of S) [ x ≈ y ] → Chain S y z → Chain S x z
_≡⟨_⟩_ {S = S} x eq = x ≈⟨ reflexive S eq ⟩_

begin[_]_ : ∀ {c p} (S : Setoid c p) {x y : Of S} → Chain S x y → S [ x ≈ y ]
begin[ S ] (x ≈⟨ eq ⟩ chain) = trans S eq (begin[ S ] chain)
begin[ S ] (x ∎) = refl S
