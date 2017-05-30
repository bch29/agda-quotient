module Quotient.ISetoid.Algebraic where

open import Quotient.Basic
open import Quotient.Setoid
open import Quotient.ISetoid
open import Quotient.Function

-- infixr 5 _×_
infixr 2 _,_

record Exists {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst

open Exists public

Σ : ∀ {c d p q} (S : Setoid c p) → ISetoid (Of S) d q → Setoid _ _
Σ S T = record
  { Of = Exists (Of S) (Of↑ T)
  ; _[_≈_] = λ x y → Exists (S [ fst x ≈ fst y ]) (λ _ → T ↑[ snd x ≈ snd y ])
  ; isEquivalence = record
    { refl = refl S , refl↑ T
    ; sym = λ eq → sym S (fst eq) , sym↑ T (snd eq)
    ; trans = λ e1 e2 → trans S (fst e1) (fst e2) , trans↑ T (snd e1) (snd e2)
    }
  }
