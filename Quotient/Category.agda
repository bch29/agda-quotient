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
    Hom : Of (Obj ⇨ Obj ⇨ Iso d q)

  _↦_ : (x y : Of Obj) → Setoid d q
  _↦_ x y = Hom ∙ x ∙ y

  field
    id′ : ∀ {x} → Of (x ↦ x)
    _∘′_ : ∀ {x y z} → Of (y ↦ z) → Of (x ↦ y) → Of (x ↦ z)

    leftId : ∀ {x y f} → (x ↦ y) [ id′ ∘′ f ≈ f ]
    rightId : ∀ {x y f} → (x ↦ y) [ f ∘′ id′ ≈ f ]
    assoc : ∀ {x y z w f} {g : Of (y ↦ z)} {h} → (x ↦ w) [ f ∘′ g ∘′ h ≈ (f ∘′ g) ∘′ h ]

  _[_∘_] = _∘′_
  _[_↦_] = _↦_

  -- recastHom : ∀ {x y x′ y′} → Obj [ x ≈ x′ ] → Obj [ y ≈ y′ ] → Of (x ↦ y ⇨ x′ ↦ y′)
  -- recastHom e1 e2 = iso₁ (cong Hom e1 e2)

open Category using (Obj; Hom; id′; _[_∘_]; _[_↦_])

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
    Obj-iso : Obj C ↔ Obj D
    Hom-iso : ∀ {x y : Of (Obj C)} → C [ x ↦ y ] ↔ D [ iso₁ Obj-iso ∙ x ↦ iso₁ Obj-iso ∙ y ]

  Hom-iso₂ : ∀ {x y : Of (Obj D)} → C [ iso₂ Obj-iso ∙ x ↦ iso₂ Obj-iso ∙ y ] ↔ D [ x ↦ y ]
  Hom-iso₂ {x} {y} =
    begin[ Iso d q ]
      C [ iso₂ Obj-iso ∙ x ↦ iso₂ Obj-iso ∙ y ]
    ≈⟨ Hom-iso ⟩
      D [ (iso₁ Obj-iso ∘ iso₂ Obj-iso) ∙ x ↦ (iso₁ Obj-iso ∘ iso₂ Obj-iso) ∙ y ]
    ≈⟨ cong (Hom D) (inverse₂ Obj-iso (refl (Obj D))) (inverse₂ Obj-iso (refl (Obj D))) ⟩
      D [ x ↦ y ]
    ∎

open CatIso public

CatSetoid : ∀ c d p q → Setoid (lsuc (c ⊔ d ⊔ p ⊔ q)) (q ⊔ (p ⊔ (d ⊔ c)))
CatSetoid c d p q = record
  { Of = Category c d p q
  ; _[_≈_] = CatIso
  ; isEquivalence = record
    { refl = record
      { Obj-iso = refl (Iso _ _)
      ; Hom-iso = refl (Iso _ _)
      }
    ; sym = λ eq → record
      { Obj-iso = sym (Iso _ _) (Obj-iso eq)
      ; Hom-iso = sym (Iso _ _) (Hom-iso₂ eq)
      }
    ; trans = λ e1 e2 → record
      { Obj-iso = trans (Iso _ _) (Obj-iso e1) (Obj-iso e2)
      ; Hom-iso = trans (Iso _ _) (Hom-iso e1) (Hom-iso e2)
      }
    }
  }

record FunctorIso {c d p q} {C D : Category c d p q} (f g : Functor C D) : Set (c ⊔ d ⊔ p ⊔ q) where
  field
    F-equiv : (Obj C ⇨ Obj D) [ F f ≈ F g ]

    Hom-iso : ∀ {x y} → D [ F f ∙ x ↦ F f ∙ y ] ↔ D [ F g ∙ x ↦ F g ∙ y ]

    fmap-equiv : ∀ {x y} → < C [ x ↦ y ] ⇨ D [ F f ∙ x ↦ F f ∙ y ]
                           , C [ x ↦ y ] ⇨ D [ F g ∙ x ↦ F g ∙ y ]
                           , ⇨-Iso (refl (Iso _ _)) Hom-iso
                           >[ fmap f ≈ fmap g ]

open FunctorIso

FunctorSetoid : ∀ {c d p q} (C D : Category c d p q) → Setoid _ _
FunctorSetoid C D = record
  { Of = Functor C D
  ; _[_≈_] = FunctorIso
  ; isEquivalence = record
    { refl = λ {f} → record
      { F-equiv = refl (Obj C ⇨ Obj D) {F f}
      ; Hom-iso = refl (Iso _ _)
      ; fmap-equiv = cong (fmap f)
      }
    ; sym = λ {f g} eq → record
      { F-equiv = λ {x} {y} e1 → sym (Obj D) (F-equiv eq (sym (Obj C) e1))
      ; Hom-iso = sym (Iso _ _) (Hom-iso eq)
      ; fmap-equiv = symHet _ _ (⇨-Iso (refl (Iso _ _)) (Hom-iso eq))
                                (fmap f) (fmap g) (fmap-equiv eq)
      }
    ; trans = λ {f g h} e1 e2 → record
      { F-equiv = λ eq → trans (Obj D) (F-equiv e1 eq) (F-equiv e2 (refl (Obj C)))
      ; Hom-iso = trans (Iso _ _) (Hom-iso e1) (Hom-iso e2)
      ; fmap-equiv = λ {x} {y} → transHet _ _ _ (⇨-Iso (refl (Iso _ _)) (Hom-iso e1))
                                                (⇨-Iso (refl (Iso _ _)) (Hom-iso e2))
                                                (fmap f) (fmap g) (fmap h)
                                                (fmap-equiv e1) (fmap-equiv e2)
      }
    }
  }

TranslateFunctor : ∀ {c d p q} {C C′ D D′ : Category c d p q} → CatIso C C′ → CatIso D D′ → Of (FunctorSetoid C D ⇨ FunctorSetoid C′ D′)
TranslateFunctor e1 e2 = record
  { _∙_ = λ f → record
    { F = iso₁ (Obj-iso e2) ∘ F f ∘ iso₂ (Obj-iso e1)
    ; fmap = {!!}
    ; fmap-id = {!!}
    ; fmap-∘ = {!!}
    }
  ; cong = {!!}
  }

FunctorCong : ∀ {c d p q} {C C′ D D′ : Category c d p q} → CatIso C C′ → CatIso D D′ → FunctorSetoid C D ↔ FunctorSetoid C′ D′
FunctorCong e1 e2 = record
  { iso₁ = TranslateFunctor e1 e2
  ; iso₂ = TranslateFunctor (sym (CatSetoid _ _ _ _) e1) (sym (CatSetoid _ _ _ _) e2)
  ; inverse₁ = {!!}
  ; inverse₂ = {!!}
  }

FunctorHom : ∀ {c d p q} → Of (CatSetoid c d p q ⇨ CatSetoid c d p q ⇨ Iso _ _)
FunctorHom = record
  { _∙_ = λ C → record
    { _∙_ = FunctorSetoid C
    ; cong = FunctorCong (refl (CatSetoid _ _ _ _))
    }
  ; cong = λ e1 e2 → FunctorCong e1 e2
  }


-- FunctorCategory : ∀ {c d p q} → Category _ {!!} _ {!!}
-- FunctorCategory {c} {d} {p} {q} = record
--   { Obj = CatSetoid c d p q
--   ; Hom = FunctorSetoid
--   ; id′ = {!!}
--   ; _∘′_ = {!!}
--   ; leftId = {!!}
--   ; rightId = {!!}
--   ; assoc = {!!}
--   }
