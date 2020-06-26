{-# OPTIONS --cubical #-}

module ELib.Gerbe.S where

open import Cubical.Foundations.Everything
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

    s : (x y : X) → (x ≡ x) → (y ≡ y)
    s x y = s-def x y .fst .fst

    isEquiv-s : (x y : X) → isEquiv (s x y)
    isEquiv-s x y = s-def x y .fst .snd

    s-eq : (x y : X) → (x ≡ x) ≃ (y ≡ y)
    s-eq x y = s x y , isEquiv-s x y

    s-carac : (x y : X) (p : x ≡ y) (q : x ≡ x) → s x y q ≡ sym p ∙ q ∙ p
    s-carac x y p q = s-def x y .snd p q

    s-id : (x : X) → s x x ≡ λ q → q
    s-id x = funExt λ q → s-carac x x refl q ∙ sym (rUnit _ ∙ lUnit _)

    s-comp : (x y z : X) → s x z ≡ s y z ∘ s x y
    s-comp x y z = recPropTrunc prop (λ py → recPropTrunc prop (λ pz →
           transport (λ i → s x (pz i) ≡ s (py i) (pz i) ∘ s x (py i)) lemma
           ) (Gerbe.conn G x z)) (Gerbe.conn G x y) where
      prop : isProp (s x z ≡ s y z ∘ s x y)
      prop = isSetΠ (λ _ → Gerbe.grpd G _ _) _ _

      lemma : s x x ≡ s x x ∘ s x x
      lemma = s-id x ∙ λ i → s-id x (~ i) ∘ s-id x (~ i)

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
