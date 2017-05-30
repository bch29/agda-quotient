module Quotient.Function where

import Function as Fun

open import Quotient.Basic
open import Quotient.Setoid
open import Quotient.ISetoid

import Relation.Binary.PropositionalEquality as PropEq

infixr 0 _→′_ _⇨_ _⟶_
infixr 8 _∘_

record Pi {c d p q} (From : Setoid c p) (To : ISetoid (Of From) d q) : Set (c ⊔ d ⊔ p ⊔ q) where
  infixl 9 _∙_

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

lift→′ : ∀ {a c p} {From : Set a} {To : Setoid c p} → (From → Of To) → Of (Prop From ⇨ To)
lift→′ {To = To} f = record
  { _∙_ = f
  ; cong = λ eq → reflexive To (PropEq.cong f eq)
  }

lift→² : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} → (A → B → C) → Of (Prop A ⇨ Prop B ⇨ Prop C)
lift→² f = lift→′ (λ x → lift→ (f x))

-- Composition and identity

_∘_ : ∀ {c d e p q r} {A : Setoid c p} {B : Setoid d q} {C : Setoid e r} → Of (B ⇨ C) → Of (A ⇨ B) → Of (A ⇨ C)
f ∘ g = record
  { _∙_ = λ x → f ∙ (g ∙ x)
  ; cong = λ eq → cong f (cong g eq)
  }

id : ∀ {c p} {S : Setoid c p} → Of (S ⇨ S)
id = record
  { _∙_ = λ x → x
  ; cong = λ eq → eq
  }

-- Setoid isomorphism and the setoid of setoids quotiented by isomorphism

infix 2 _↔_

record _↔_ {c d p q} (S : Setoid c p) (T : Setoid d q) : Set (c ⊔ d ⊔ p ⊔ q) where
  field
    iso₁ : Of (S ⇨ T)
    iso₂ : Of (T ⇨ S)

    inverse₁ : (S ⇨ S) [ iso₂ ∘ iso₁ ≈ id ]
    inverse₂ : (T ⇨ T) [ iso₁ ∘ iso₂ ≈ id ]

open _↔_ public

Iso : ∀ c p → Setoid (lsuc (c ⊔ p)) (c ⊔ p)
Iso c p = record
  { Of = Setoid c p
  ; _[_≈_] = _↔_
  ; isEquivalence = record
    { refl = record
      { iso₁ = id
      ; iso₂ = id
      ; inverse₁ = λ x → x
      ; inverse₂ = λ x → x
      }
    ; sym = λ iso → record
      { iso₁ = iso₂ iso
      ; iso₂ = iso₁ iso
      ; inverse₁ = inverse₂ iso
      ; inverse₂ = inverse₁ iso
      }
    ; trans = λ {S} {T} {U} i1 i2 → record
      { iso₁ = iso₁ i2 ∘ iso₁ i1
      ; iso₂ = iso₂ i1 ∘ iso₂ i2
      ; inverse₁ = λ {x y} eq →
        begin[ S ]
          ((iso₂ i1 ∘ iso₂ i2) ∘ (iso₁ i2 ∘ iso₁ i1)) ∙ x
        ≈⟨ cong (iso₂ i1) (inverse₁ i2 (refl T )) ⟩
          (iso₂ i1 ∘ iso₁ i1) ∙ x
        ≈⟨ inverse₁ i1 eq ⟩
          y
        ∎
      ; inverse₂ = λ {x y} eq →
        begin[ U ]
          ((iso₁ i2 ∘ iso₁ i1) ∘ (iso₂ i1 ∘ iso₂ i2)) ∙ x
        ≈⟨ cong (iso₁ i2) (inverse₂ i1 (refl T)) ⟩
          (iso₁ i2 ∘ iso₂ i2) ∙ x
        ≈⟨ inverse₂ i2 eq ⟩
          y
        ∎
      }
    }
  }

-- Setoid isomorphism respects the function arrow

dimap : ∀ {c d e f p q r s} {S : Setoid c p} {T : Setoid d q} {U : Setoid e r} {V : Setoid f s} → Of (T ⇨ S) → Of (U ⇨ V) → Of ((S ⇨ U) ⇨ (T ⇨ V))
dimap f g = record
  { _∙_ = λ h → g ∘ h ∘ f
  ; cong = λ e1 e2 → cong g (e1 (cong f e2))
  }

⇨-Iso : ∀ {c c′ d d′ p p′ q q′} {S : Setoid c p} {T : Setoid c′ p′} {U : Setoid d q} {V : Setoid d′ q′} → S ↔ T → U ↔ V → (S ⇨ U) ↔ (T ⇨ V)
⇨-Iso {S = S} {T} {U} {V} s∼t u∼v = record
  { iso₁ = dimap (iso₂ s∼t) (iso₁ u∼v)
  ; iso₂ = dimap (iso₁ s∼t) (iso₂ u∼v)
  ; inverse₁ = λ e1 e2 → inverse₁ u∼v (e1 (inverse₁ s∼t e2))
  ; inverse₂ = λ e1 e2 → inverse₂ u∼v (e1 (inverse₂ s∼t e2))
  }

-- cong-refl : ∀ {c d} {S T : Of (Iso c d)} → Iso c d [ S ≈ T ] → 

cong-iso : ∀ {c d p q} (S : Setoid c p) (P : Of (S ⇨ Iso d q)) (x : Of S) → (P ∙ x) ↔ (P ∙ x)
cong-iso S P x = cong P (refl S)

-- This is not true!

-- cong-refl : ∀ {c d p q} (S : Setoid c p) (P : Of (S ⇨ Iso d q)) (x : Of S) → (P ∙ x ⇨ P ∙ x) [ iso₁ (cong-iso S P x) ≈ id ]
-- cong-refl S P x {y} {z} eq =
--   begin[ P ∙ x ]
--     iso₁ (cong-iso S P x) ∙ y
--   ≈⟨ {!!} ⟩
--     (iso₂ (cong-iso S P x) ∘ iso₁ (cong-iso S P x)) ∙ y
--   ≈⟨ inverse₁ (cong-iso S P x) eq ⟩
--     z
--   ∎

-- Heterogeneous Equality

<_,_,_>[_≈_] : ∀ {c p} (S T : Setoid c p) → S ↔ T → Of S → Of T → Set p
< S , T , iso >[ x ≈ y ] = T [ iso₁ iso ∙ x ≈ y ]

symHet : ∀ {c p} (S T : Setoid c p) (iso : S ↔ T) (x : Of S) (y : Of T) → < S , T , iso >[ x ≈ y ] → < T , S , sym (Iso _ _) iso >[ y ≈ x ]
symHet S T iso x y eq =
  begin[ S ]
    iso₂ iso ∙ y
  ≈⟨ cong (iso₂ iso) (sym T eq) ⟩
    (iso₂ iso ∘ iso₁ iso) ∙ x
  ≈⟨ inverse₁ iso (refl S) ⟩
    x
  ∎

transHet : ∀ {c p} (S T U : Setoid c p) (i1 : S ↔ T) (i2 : T ↔ U) (x : Of S) (y : Of T) (z : Of U) → < S , T , i1 >[ x ≈ y ] → < T , U , i2 >[ y ≈ z ] → < S , U , trans (Iso _ _) i1 i2 >[ x ≈ z ]
transHet S T U i1 i2 x y z e1 e2 =
  begin[ U ]
    iso₁ i2 ∙ (iso₁ i1 ∙ x)
  ≈⟨ cong (iso₁ i2) e1 ⟩
    iso₁ i2 ∙ y
  ≈⟨ e2 ⟩
    z
  ∎
