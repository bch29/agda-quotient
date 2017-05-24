module Quotient.ISetoid where

open import Quotient.Setoid.Core
open import Quotient.ISetoid.Core public

_at_ : ∀ {ℓ c p} {I : Set ℓ} → ISetoid I c p → I → Setoid c p
S at i = record
  { Of = Of↑ S i
  ; _[_≈_] = S ↑[_≈_]
  ; isEquivalence = record
    { refl = refl↑ S
    ; sym = sym↑ S
    ; trans = trans↑ S
    }
  }
