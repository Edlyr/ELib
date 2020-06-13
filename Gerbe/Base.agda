{-# OPTIONS --cubical #-}

module ELib.Gerbe.Base where

open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc ; elim to elimPropTrunc)
--open import Cubical.Homotopy.Loopspace
--open import Cubical.Structures.Group
open import Cubical.Structures.Group hiding (⟨_⟩)
open import Cubical.Structures.AbGroup renaming (⟨_⟩ to Ab⟨_⟩)
open import ELib.Group.Morphism
open import Cubical.Data.Sigma
--open import ELib.B1.MorphismDelooping
--open import ELib.UsefulLemmas
open import Cubical.Functions.Embedding
open import ELib.UsefulLemmas

private
  variable
    ℓ ℓ' ℓ'' : Level

isSetGroupIso : ∀ {ℓ ℓ' : Level} (G₁ : Group {ℓ}) (G₂ : Group {ℓ'}) → isSet (GroupIso G₁ G₂)
isSetGroupIso G₁ G₂ = isSetΣ (isSetΣ (isOfHLevelΠ 2 λ _ → group-is-set G₂) λ _ → isProp→isSet (isPropIsEquiv _)) λ _ → isProp→isSet (isPropIsGroupHom G₁ G₂)


isGerbe : Type ℓ → Type ℓ
isGerbe X = ∥ X ∥ × isGroupoid X × ((x y : X) → ∥ x ≡ y ∥) × ((x : X) → (p q : x ≡ x) → p ∙ q ≡ q ∙ p)

Gerbe : Type (ℓ-suc ℓ)
Gerbe {ℓ} = Σ (Type ℓ) isGerbe

⟨_⟩ : Gerbe → Type ℓ
⟨_⟩ = fst

gerbe-inhabited : (G : Gerbe {ℓ}) → ∥ ⟨ G ⟩ ∥
gerbe-inhabited G = fst (snd G)

gerbe-grpd : (G : Gerbe {ℓ}) → isGroupoid ⟨ G ⟩
gerbe-grpd G = fst (snd (snd G))

gerbe-conn : (G : Gerbe {ℓ}) → ((x y : ⟨ G ⟩) → ∥ x ≡ y ∥)
gerbe-conn G = fst (snd (snd (snd G)))

gerbe-comm : (G : Gerbe {ℓ}) → ((x : ⟨ G ⟩) → (p q : x ≡ x) → p ∙ q ≡ q ∙ p)
gerbe-comm G = snd (snd (snd (snd G)))

π : (G : Gerbe {ℓ}) (x : ⟨ G ⟩) → AbGroup {ℓ}
π G x = (x ≡ x) , _∙_ , ((gerbe-grpd G _ _ , assoc) , refl , (λ x → sym (rUnit x) , sym (lUnit x)) , λ x → sym x , rCancel x , lCancel x) , gerbe-comm G x

module S (G : Gerbe {ℓ}) where
  X = ⟨ G ⟩

  s-type : (x y : X) → Type ℓ
  s-type x y = Σ[ f ∈ ((x ≡ x) ≃ (y ≡ y)) ] ((p : x ≡ y) (q : x ≡ x) → f .fst q ≡ sym p ∙ q ∙ p)

  abstract
    s : (x y : X) → s-type x y
    s x y = fst (T x y) where
      T : (x y : X) → isContr (s-type x y)
      T x y = recPropTrunc isPropIsContr (λ x≡y → transport (λ i → isContr (s-type x (x≡y i))) base-case) (gerbe-conn G x y) where
        base-case : isContr (s-type x x)
        base-case = center , contr where
          center : s-type x x
          center = idEquiv _ , λ p q → sym (cong (λ r → (sym p) ∙ r) (gerbe-comm G x q p) ∙ compPathl-cancel _ _)

          contr : (f : s-type x x) → center ≡ f
          contr (f , !) = ΣProp≡ (λ f → isPropΠ2 λ p q → gerbe-grpd G _ _ _ _) id≡f where
            id≡f : fst center ≡ f
            id≡f = equivEq _ _ (funExt λ q → rUnit _ ∙ lUnit _ ∙ sym (! refl q))

  s-iso : (x y : X) → GroupIso (AbGroup→Group (π G x)) (AbGroup→Group (π G y))
  s-iso x y = s x y .fst , morph where
    H = AbGroup→Group (π G x)
    H' = AbGroup→Group (π G y)
    f = s x y .fst .fst
    ! : (r : x ≡ y) → _
    ! = s x y .snd
    _⋆_ = group-operation H
    _⨀_ = group-operation H'
    morph : isGroupHom H H' (fst (s x y .fst))
    morph = λ p q → recPropTrunc (group-is-set H' _ _) (λ r → 
      f (p ⋆ q)                            ≡⟨ ! r (p ∙ q) ⟩
      sym r ∙ (p ∙ q) ∙ r                  ≡⟨ (λ i → sym r ∙ (assoc p q r (~ i))) ⟩
      sym r ∙ p ∙ q ∙ r                    ≡⟨ cong (λ x → sym r ∙ p ∙ x ∙ r) (sym (compPathl-cancel r q)) ⟩
      sym r ∙ p ∙ (r ∙ sym r ∙ q) ∙ r      ≡⟨ cong (λ x → sym r ∙ p ∙ x) (sym (assoc _ _ _) ∙ cong (λ y → r ∙ y) (sym (assoc _ _ _))) ⟩
      sym r ∙ p ∙ r ∙ sym r ∙ q ∙ r        ≡⟨ assoc _ _ _ ∙ assoc _ _ _ ∙ cong (λ x → x ∙ sym r ∙ q ∙ r) (sym (assoc _ _ _)) ⟩
      (sym r ∙ p ∙ r) ∙ (sym r ∙ q ∙ r)    ≡⟨ sym (λ i → ! r p i ∙ ! r q i) ⟩
      f p ⨀ f q ∎) (gerbe-conn G x y)
