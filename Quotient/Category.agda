module Quotient.Category where

open import Quotient.Basic
open import Quotient.Setoid
open import Quotient.ISetoid
open import Quotient.Function

record Category c d p q : Set (lsuc (c ⊔ d ⊔ p ⊔ q)) where
  infixr 1 _↦_
  infixr 8 _∘′_

  field
    Obj : Setoid c p
    Morph : Of (Obj ⇨ Obj ⇨ TwoSetoid d q)

  _↦_ : (x y : Of Obj) → Setoid d q
  _↦_ x y = Morph ∙ x ∙ y

  field
    id′ : ∀ {x} → Of (x ↦ x)
    _∘′_ : ∀ {x y z} → Of (y ↦ z) → Of (x ↦ y) → Of (x ↦ z)

    leftId : ∀ {x y f} → (x ↦ y) [ id′ ∘′ f ≈ f ]
    rightId : ∀ {x y f} → (x ↦ y) [ f ∘′ id′ ≈ f ]
    assoc : ∀ {x y z w f} {g : Of (y ↦ z)} {h} → (x ↦ w) [ f ∘′ g ∘′ h ≈ (f ∘′ g) ∘′ h ]

  _[_∘_] = _∘′_
  _[_↦_] = _↦_

  -- recastMorph : ∀ {x y x′ y′} → Obj [ x ≈ x′ ] → Obj [ y ≈ y′ ] → Of (x ↦ y ⇨ x′ ↦ y′)
  -- recastMorph e1 e2 = iso₁ (cong Morph e1 e2)

open Category using (Obj; Morph; id′; _[_∘_]; _[_↦_])

record Functor {c d p q} (C : Category c d p q) (D : Category c d p q) : Set (c ⊔ d ⊔ p ⊔ q) where
  field
    F : Of (Obj C ⇨ Obj D)
    fmap : ∀ {x y} → Of (C [ x ↦ y ] ⇨ D [ F ∙ x ↦ F ∙ y ])

    fmap-id : ∀ {x} → (D [ F ∙ x ↦ F ∙ x ]) [ fmap ∙ id′ C ≈ id′ D ]
    fmap-∘ : ∀ {x y z} {f : Of (C [ y ↦ z ])} {g : Of (C [ x ↦ y ])}
             → (D [ F ∙ x ↦ F ∙ z ]) [ D [ fmap ∙ f ∘ fmap ∙ g ] ≈ fmap ∙ C [ f ∘ g ] ]

open Functor public

record CatIso {c d p q} (C D : Category c d p q) : Set (c ⊔ d ⊔ p ⊔ q) where
  field
    Obj-iso : Iso (Obj C) (Obj D)
    Morph-iso : ∀ {x y : Of (Obj C)} → Iso (C [ x ↦ y ]) (D [ iso₁ Obj-iso ∙ x ↦ iso₁ Obj-iso ∙ y ])

  Morph-iso₂ : ∀ {x y : Of (Obj D)} → Iso (C [ iso₂ Obj-iso ∙ x ↦ iso₂ Obj-iso ∙ y ]) (D [ x ↦ y ])
  Morph-iso₂ {x} {y} =
    begin[ TwoSetoid d q ]
      C [ iso₂ Obj-iso ∙ x ↦ iso₂ Obj-iso ∙ y ]
    ≈⟨ Morph-iso ⟩
      D [ (iso₁ Obj-iso ∘ iso₂ Obj-iso) ∙ x ↦ (iso₁ Obj-iso ∘ iso₂ Obj-iso) ∙ y ]
    ≈⟨ cong (Morph D) (inverse₂ Obj-iso (refl (Obj D))) (inverse₂ Obj-iso (refl (Obj D))) ⟩
      D [ x ↦ y ]
    ∎

open CatIso public

CatSetoid : ∀ c d p q → Setoid (lsuc (c ⊔ d ⊔ p ⊔ q)) (q ⊔ (p ⊔ (d ⊔ c)))
CatSetoid c d p q = record
  { Of = Category c d p q
  ; _[_≈_] = CatIso
  ; isEquivalence = record
    { refl = record
      { Obj-iso = refl (TwoSetoid _ _)
      ; Morph-iso = refl (TwoSetoid _ _)
      }
    ; sym = λ eq → record
      { Obj-iso = sym (TwoSetoid _ _) (Obj-iso eq)
      ; Morph-iso = sym (TwoSetoid _ _) (Morph-iso₂ eq)
      }
    ; trans = λ e1 e2 → record
      { Obj-iso = trans (TwoSetoid _ _) (Obj-iso e1) (Obj-iso e2)
      ; Morph-iso = trans (TwoSetoid _ _) (Morph-iso e1) (Morph-iso e2)
      }
    }
  }

-- Fmaps : ∀ {c d p q} {C D : Category c d p q} → ISetoid (Functor C D) _ _
-- Fmaps {C = C} {D} = record
--   { Of↑ = λ f → ∀ {x y} → Of (C [ x ↦ y ] ⇨ D [ F f ∙ x ↦ F f ∙ y ])
--   ; _↑[_≈_] = λ m1 m2 → Iso {!!} {!!}
--   ; isEquivalence↑ = {!!}
--   }

record FunctorIso {c d p q} {C D : Category c d p q} (f g : Functor C D) : Set {!!} where
  field
    F-equiv : (Obj C ⇨ Obj D) [ F f ≈ F g ]

  fmapg : ∀ {x y} → Of (C [ x ↦ y ] ⇨ D [ F f ∙ x ↦ F f ∙ y ])
  fmapg {x} {y} = iso₂ (⇨-Iso (refl {!(C [ x ↦ y ])!}) {!!} ) ∙ fmap g

  -- field
  --   fmap-equiv : ∀ {x y} → (C [ x ↦ y ] ⇨ D [ F f ∙ x ↦ F f ∙ y ]) [ fmap f ≈ {!iso₂ (cong (Morph D) ? ?) ∙ fmap g!} ]

-- FunctorSetoid : ∀ {c d p q} (C D : Category c d p q) → Setoid _ {!!}
-- FunctorSetoid C D = record
--   { Of = Functor C D
--   ; _[_≈_] = FunctorIso
--   ; isEquivalence = record
--     { refl = {!!}
--     ; sym = {!!}
--     ; trans = {!!}
--     }
--   }


-- FunctorCategory : ∀ {c d p q} → Category _ {!!} _ {!!}
-- FunctorCategory {c} {d} {p} {q} = record
--   { Obj = CatSetoid c d p q
--   ; Morph = {!FunctorSetoid!}
--   ; id′ = {!!}
--   ; _∘′_ = {!!}
--   ; leftId = {!!}
--   ; rightId = {!!}
--   ; assoc = {!!}
--   }
