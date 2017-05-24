module Quotient.Function where

import Function as Fun

open import Quotient.Basic
open import Quotient.Setoid
open import Quotient.ISetoid

import Relation.Binary.PropositionalEquality as PropEq

record Pi {c d p q} (From : Setoid c p) (To : ISetoid (Of From) d q) : Set (c ⊔ d ⊔ p ⊔ q) where
  infixl 0 _∙_

  field
    _∙_ : (x : Of From) → Of↑ To x

  app = _∙_

  field
    cong : ∀ {x y} → From [ x ≈ y ] → To ↑[ app x ≈ app y ]

open Pi public

Π : ∀ {c d p q} (From : Setoid c p) (To : ISetoid (Of From) d q) → Setoid _ _
Π From To = record
  { Of = Pi From To
  ; _[_≈_] = λ f g → ∀ {x y} → From [ x ≈ y ] → To ↑[ app f x ≈ app g y ]
  ; isEquivalence = record
    { refl = λ {f} eq → cong f eq
    ; sym = λ {f g} e1 e2 → sym↑ To (e1 (sym From e2))
    ; trans = λ {f g h} e1 e2 eq → trans↑ To (e1 eq) (e2 (refl From))
    }
  }

_⇨_ : ∀ {c d p q} (From : Setoid c p) (To : Setoid d q) → Setoid _ _
From ⇨ To = Π From (indexed _ To)

_⟶_ : ∀ {c d p q} (From : Setoid c p) (To : Setoid d q) → Set _
From ⟶ To = Of (From ⇨ To)

_→′_ : ∀ {a b} (From : Set a) (To : Set b) → Setoid _ _
From →′ To = Prop From ⇨ Prop To

lift→ : ∀ {a b} {From : Set a} {To : Set b} → (From → To) → Of (From →′ To)
lift→ f = record
  { _∙_ = f
  ; cong = PropEq.cong f
  }

_∘_ : ∀ {c d e p q r} {A : Setoid c p} {B : Setoid d q} {C : Setoid e r} → Of (B ⇨ C) → Of (A ⇨ B) → Of (A ⇨ C)
f ∘ g = record
  { _∙_ = λ x → f ∙ (g ∙ x)
  ; cong = λ eq → cong f (cong g eq)
  }

id : ∀ {c p} {S : Setoid c p} : Of (S ⇨ S)
id
