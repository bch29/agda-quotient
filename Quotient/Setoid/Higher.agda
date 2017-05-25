module Quotient.Setoid.Higher where

open import Quotient.Prelude

Higher : ∀ {c p} (S : Setoid c p) → ISetoid (Of (S × S)) _ _
Higher S = record
  { Of↑ = λ { (x , y) → S [ x ≈ y ]}
  ; _↑[_≈_] = λ {x} {y} _ _ → (S × S) [ x ≈ y ]
  ; isEquivalence↑ = record
    { refl = refl (S × S)
    ; sym = sym (S × S)
    ; trans = trans (S × S)
    }
  }
