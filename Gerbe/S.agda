{-# OPTIONS --cubical #-}

module ELib.Gerbe.S where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism

open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc ; elim to elimPropTrunc)
open import Cubical.Data.Sigma
open import Cubical.Structures.Group hiding (⟨_⟩)
open import Cubical.Structures.AbGroup renaming (⟨_⟩ to Ab⟨_⟩ ; AbGroup→Group to GRP)

open import ELib.Gerbe.Base

private
  variable
    ℓ ℓ' : Level

module S (G : Gerbe {ℓ}) where
  X = ⟨ G ⟩

  s-type : (x y : X) → Type ℓ
  s-type x y = Σ[ f ∈ ((x ≡ x) ≃ (y ≡ y)) ] ((p : x ≡ y) (q : x ≡ x) → f .fst q ≡ sym p ∙ q ∙ p)

  abstract
    s-def : (x y : X) → s-type x y
    s-def x y = fst (T x y) where
      T : (x y : X) → isContr (s-type x y)
      T x y = recPropTrunc isPropIsContr (λ x≡y → transport (λ i → isContr (s-type x (x≡y i))) base-case) (Gerbe.conn G x y) where
        base-case : isContr (s-type x x)
        base-case = center , contr where
          center : s-type x x
          center = idEquiv _ , λ p q → sym (cong (λ r → (sym p) ∙ r) (Gerbe.comm G x q p) ∙ compPathl-cancel _ _)

          contr : (f : s-type x x) → center ≡ f
          contr (f , !) = Σ≡Prop (λ f → isPropΠ2 λ p q → Gerbe.grpd G _ _ _ _) id≡f where
            id≡f : fst center ≡ f
            id≡f = equivEq _ _ (funExt λ q → rUnit _ ∙ lUnit _ ∙ sym (! refl q))

  abstract
    s : (x y : X) → (x ≡ x) → (y ≡ y)
    s x y = s-def x y .fst .fst

    isEquiv-s : (x y : X) → isEquiv (s x y)
    isEquiv-s x y = s-def x y .fst .snd


    s-carac : (x y : X) (p : x ≡ y) (q : x ≡ x) → s x y q ≡ sym p ∙ q ∙ p
    s-carac x y p q = s-def x y .snd p q

    s-id : (x : X) → s x x ≡ λ q → q
    s-id x = funExt λ q → s-carac x x refl q ∙ sym (rUnit _ ∙ lUnit _)

  s-eq : (x y : X) → (x ≡ x) ≃ (y ≡ y)
  s-eq x y = s x y , isEquiv-s x y
  abstract
    s-comp : (x y z : X) → s x z ≡ s y z ∘ s x y
    s-comp x y z = recPropTrunc prop (λ py → recPropTrunc prop (λ pz →
           transport (λ i → s x (pz i) ≡ s (py i) (pz i) ∘ s x (py i)) lemma
           ) (Gerbe.conn G x z)) (Gerbe.conn G x y) where
      prop : isProp (s x z ≡ s y z ∘ s x y)
      prop = isSetΠ (λ _ → Gerbe.grpd G _ _) _ _

      lemma : s x x ≡ s x x ∘ s x x
      lemma = s-id x ∙ λ i → s-id x (~ i) ∘ s-id x (~ i)

  abstract
    s-inv : (x y : X) → invEq (s-eq x y) ≡ s y x
    s-inv x y = recPropTrunc prop (λ p → transport (λ i → invEq (s-eq x (p i)) ≡ s (p i) x) lemma) (Gerbe.conn G x y) where
      prop : isProp (invEq (s-eq x y) ≡ s y x)
      prop = isSetΠ (λ _ → Gerbe.grpd G _ _) _ _

      lemma : invEq (s-eq x x) ≡ s x x
      lemma =
        invEq (s-eq x x)
          ≡⟨ cong invEq (equivEq (s-eq x x) (idEquiv _) (s-id x)) ⟩
        invEq (idEquiv _)
          ≡⟨ cong equivFun (invEquivIdEquiv _) ⟩
        (λ q → q)
          ≡⟨ sym (s-id x) ⟩
        s x x ∎

  abstract
    isHom-s : (x y : X) → isGroupHom (GRP (π G x)) (GRP (π G y)) (s x y)
    isHom-s x y = recPropTrunc prop (λ p →
      transport (λ i → isGroupHom (GRP (π G x)) (GRP (π G (p i))) (s x (p i))) lemma)
      (Gerbe.conn G x y) where
      prop : isProp _
      prop = isPropIsGroupHom (GRP (π G x)) (GRP (π G y))

      lemma : isGroupHom (GRP (π G x)) (GRP (π G x)) (s x x)
      lemma p q =
        s x x (p ∙ q)
          ≡⟨ (λ i → s-id x i (p ∙ q)) ⟩
        p ∙ q
          ≡⟨ (λ i → s-id x (~ i) p ∙ s-id x (~ i) q) ⟩
        s x x p ∙ s x x q ∎

  s-hom : (x y : X) → AbGroupHom (π G x) (π G y)
  s-hom x y = grouphom (s x y) (isHom-s x y)

  s-groupEquiv : (x y : X) → AbGroupEquiv (π G x) (π G y)
  s-groupEquiv x y = groupequiv (s-eq x y) (isHom-s x y)

open import ELib.B1.MorphismDelooping
module test-deloop (G : Gerbe {ℓ}) (H : Gerbe {ℓ'}) (a : ⟨ G ⟩) (b : ⟨ H ⟩) where
  module Deloop = Delooping (Gerbe.conn G) (Gerbe.grpd H) {a = a} {b = b}
  open S H
  G∙ : Pointed _
  G∙ = ⟨ G ⟩ , a
  H∙ : Pointed _
  H∙ = ⟨ H ⟩ , b
  eq→ : (G∙ →∙ H∙) → AbGroupHom (π G a) (π H b)
  eq→ (g , p) = compGroupHom (grouphom (cong g) (cong-∙ g)) (s-hom (g a) b)

  eq← : AbGroupHom (π G a) (π H b) → G∙ →∙ H∙
  eq← f = deloop .fst , sym (deloop .snd .fst) where
    open GroupHom
    open Deloop (fun f) (isHom f)

  abstract
    sec : section eq→ eq←
    sec fhom =
      groupHomEq (s (g a) b ∘ cong g
        ≡⟨ cong (s (g a) b ∘_) (funExt λ q → sym (compPathl-cancel _ _) ∙ cong (sym p ∙_) (! q)) ⟩
      s (g a) b ∘ (λ q → sym p ∙ f q ∙ p)
        ≡⟨ cong (s (g a) b ∘_) (cong (_∘ f) (sym (funExt (s-carac _ _ p)))) ⟩
      s (g a) b ∘ s b (g a) ∘ f
        ≡⟨ cong (_∘ f) (sym (s-comp _ _ _) ∙ s-id _) ⟩
      f ∎) where
      f = GroupHom.fun fhom
      hom = GroupHom.isHom fhom
      g = eq← (grouphom f hom) .fst
      del = Deloop.deloop f hom
      p = del .snd .fst
      ! = del .snd .snd

    retr : retract eq→ eq←
    retr (g , p) = ΣPathP (cong fst deloop≡ , λ i → sym (lemma i)) where
      f = GroupHom.fun (eq→ (g , p))
      hom = GroupHom.isHom (eq→ (g , p))
      deloop1 = Deloop.deloop f hom
      deloop2 : Deloop.deloopingType f hom
      deloop2 = g , sym p , λ q →
        (sym p ∙ cong g q)
          ≡⟨ sym (compPathr-cancel _ _) ∙ cong (_∙ sym p) (sym (assoc _ _ _)) ⟩
        (sym p ∙ cong g q ∙ p) ∙ sym p
          ≡⟨ cong (_∙ sym p) (sym (s-carac _ _ _ _)) ⟩
        s (g a) b (cong g q) ∙ sym p ∎
      deloop≡ : deloop1 ≡ deloop2
      deloop≡ = Deloop.propDeloop f hom _ _
      lemma : PathP (λ i → b ≡ fst (deloop≡ i) a) (deloop1 .snd .fst) (sym p)
      lemma = λ i → fst (snd (deloop≡ i))

  equiv : (G∙ →∙ H∙) ≃ AbGroupHom (π G a) (π H b)
  equiv = isoToEquiv (iso eq→ eq← sec retr)

  isSet→∙ : isSet (G∙ →∙ H∙)
  isSet→∙ = isOfHLevelRespectEquiv 2 (invEquiv equiv) isSetGroupHom
