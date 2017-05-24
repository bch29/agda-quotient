module Quotient.Setoid where

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
