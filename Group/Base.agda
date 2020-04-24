{-# OPTIONS --cubical #-}

module ELib.Group.Base where

open import Cubical.Foundations.Prelude hiding (comp)

record GroupStruct {ℓ} (A : Type ℓ) : Type ℓ where
  constructor struct-group
  field
    set : isSet A
    id : A
    inv : A → A
    comp : A → A → A
    lUnit : (a : A) → a ≡ comp id a
    lCancel : (a : A) → comp (inv a) a ≡ id
    assoc : (a b c : A) → comp (comp a b) c ≡ comp a (comp b c)

  --private
  _⨀_ = comp
  
  simplL : (a : A) {b c : A} → a ⨀ b ≡ a ⨀ c → b ≡ c
  simplL a {b} {c} p = lUnit b ∙ cong (λ x → comp x b) (sym (lCancel a)) ∙ assoc _ _ _ ∙ cong (λ x → inv a ⨀ x) p ∙ (sym (assoc _ _ _)) ∙ cong (λ x → x ⨀ c) (lCancel a) ∙ sym (lUnit c)
  
  rCancel : (a : A) → a ⨀ (inv a) ≡ id
  rCancel a =
    a ⨀ inv a
      ≡⟨ lUnit _ ∙ cong (λ x → x ⨀ (a ⨀ inv a)) (sym (lCancel (inv a))) ⟩
    (inv (inv a) ⨀ inv a) ⨀ (a ⨀ inv a)
      ≡⟨ assoc _ _ _ ∙ cong (λ x → inv (inv a) ⨀ x) (sym (assoc _ _ _)) ⟩
    inv (inv a) ⨀ ((inv a ⨀ a) ⨀ inv a)
      ≡⟨ cong (λ x → inv (inv a) ⨀ x) (cong (λ x → x ⨀ inv a) (lCancel a) ∙ sym (lUnit (inv a))) ⟩
    inv (inv a) ⨀ (inv a)
      ≡⟨ lCancel (inv a) ⟩
    id ∎

  invInvo : (a : A) → inv (inv a) ≡ a
  invInvo a = simplL (inv a) (rCancel _ ∙ sym (lCancel _))

  rUnit : (a : A) → a ≡ a ⨀ id
  rUnit a = lUnit a ∙ cong (λ x → x ⨀ a) (sym (lCancel (inv a))) ∙ assoc _ _ _ ∙ λ i → (invInvo a i) ⨀ (lCancel a i)

  simplR : {a b : A} (c : A) → a ⨀ c ≡ b ⨀ c → a ≡ b
  simplR {a} {b} c p = rUnit a ∙ (cong (λ x → a ⨀ x) (sym (rCancel c))) ∙ sym (assoc _ _ _) ∙ cong (λ x → x ⨀ (inv c)) p ∙ assoc _ _ _ ∙ cong (λ x → b ⨀ x) (rCancel c) ∙ sym (rUnit b)

  invId : inv id ≡ id
  invId = simplL id (rCancel id ∙ lUnit id)

  idUniqueL : (e x : A) → e ⨀ x ≡ x → e ≡ id
  idUniqueL e x p = simplR x (p ∙ lUnit _)

  idUniqueR : (x e : A) → x ⨀ e ≡ x → e ≡ id
  idUniqueR x e p = simplL x (p ∙ rUnit _)

  invUniqueL : (g h : A) → g ⨀ h ≡ id → g ≡ inv h
  invUniqueL g h p = simplR h (p ∙ sym (lCancel h))

  invUniqueR : (g h : A) → g ⨀ h ≡ id → h ≡ inv g
  invUniqueR g h p = simplL g (p ∙ sym (rCancel g))

  diff : A → A → A
  diff a b = a ⨀ (inv b)

record Group ℓ : Type (ℓ-suc ℓ) where
  constructor group
  field
    type : Type ℓ
    struct : GroupStruct type

  open GroupStruct struct public

--open import Cubical.Foundations.Everything

isMorphism : {ℓ ℓ' : Level} (G : Group ℓ) (H : Group ℓ') → (Group.type G → Group.type H) → Type (ℓ-max ℓ ℓ')
isMorphism G H f = (x y : Group.type G) → f (Group.comp G x y) ≡ Group.comp H (f x) (f y)

Hom : {ℓ ℓ' : Level} (G : Group ℓ) (H : Group ℓ') → Type (ℓ-max ℓ ℓ')
Hom G H = Σ[ f ∈ (Group.type G → Group.type H) ] isMorphism G H f

homId : {ℓ ℓ' : Level} (G : Group ℓ) (H : Group ℓ') (f : Hom G H) → (fst f (Group.id G)) ≡ Group.id H
homId Ggrp Hgrp (f , morph) = H.simplL (f G.id) (
  f G.id H.⨀ f G.id
    ≡⟨ sym (morph G.id G.id) ⟩
  f (G.id G.⨀ G.id)
    ≡⟨ cong f (sym (G.lUnit _))  ⟩
  f G.id
    ≡⟨ H.rUnit _ ⟩
  f G.id H.⨀ H.id ∎) where
  module G = Group Ggrp
  module H = Group Hgrp

homInv : {ℓ ℓ' : Level} (G : Group ℓ) (H : Group ℓ')
  (f : Hom G H) (x : Group.type G) → fst f (Group.inv G x) ≡ Group.inv H (fst f x)
homInv Ggrp Hgrp f x = H.invUniqueL _ _ (sym (snd f (G.inv x) x) ∙ cong (fst f) (G.lCancel x) ∙ homId Ggrp Hgrp f ) where
  module G = Group Ggrp
  module H = Group Hgrp
------------------
--open import Cubical.Foundations.Everything

--G-Setᵃᵇˢ : ∀ {ℓ} → Group ℓ → Type (ℓ-suc ℓ)
--G-Setᵃᵇˢ {ℓ} Ggrp = Σ[ χ ∈ (hSet ℓ) ] Hom Ggrp {!!}
