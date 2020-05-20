{-# OPTIONS --cubical #-}

module ELib.B1.TorsorGroupoid where

open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc)
open import Cubical.HITs.SetTruncation
open import Cubical.Data.Sigma
open import Cubical.Structures.Group
open import ELib.B1.Torsor
open import ELib.UsefulLemmas

module BTorsor {ℓ : Level} {Ggrp : Group {ℓ}} where
  module G = GroupLemmas Ggrp
  B : Type (ℓ-suc ℓ)
  B = Σ[ r ∈ (RAction Ggrp) ] ∥ principalTorsor Ggrp ≡ r ∥

  actionLaw : (T : B) → fst (fst T) → ⟨ Ggrp ⟩ → fst (fst T)
  actionLaw T x g = fst (snd (fst T)) x g
  syntax actionLaw T x g = x ⋆⟨ T ⟩ g

  T⟨_⟩ : B → Type ℓ
  T⟨ X ⟩ = fst (fst X) 

  isTorsorBElement : (x : B) → isTorsor Ggrp (fst x)
  isTorsorBElement (r , p) = recPropTrunc (isPropIsTorsor Ggrp r) (λ p → transport (cong (isTorsor Ggrp) p) (isTorsorPrincipalTorsor Ggrp)) p

  isSetBElement : (x : B) → isSet (fst (fst x))
  isSetBElement x = fst (snd (isTorsorBElement x))

  caracB≡ : (X Y : B) → (X ≡ Y) ≃ (Σ[ f ∈ T⟨ X ⟩ ≃ T⟨ Y ⟩ ] ((x : _) (g : _) → equivFun f (x ⋆⟨ X ⟩ g) ≡ equivFun f x ⋆⟨ Y ⟩ g))
  caracB≡ X Y =
    X ≡ Y
      ≃⟨ isoToEquiv (iso (cong fst) (ΣProp≡ λ _ → propTruncIsProp) (λ _ → refl)
         (λ p → cong ΣPathP (ΣProp≡ (λ _ → isOfHLevelPathP 1 (λ i → propTruncIsProp) _ _) refl))) ⟩
    fst X ≡ fst Y
      ≃⟨ TorsorEquality.torsorEqualityEquiv Ggrp (fst X) (fst Y) (isTorsorBElement X) (isTorsorBElement Y) ⟩
    _ ■

  isGroupoidB : isGroupoid B
  isGroupoidB X Y =
    isOfHLevelRespectEquiv 2 (invEquiv (caracB≡ X Y))
    (isSetΣ (isOfHLevel≃ 2 (isSetBElement X) (isSetBElement Y)) λ _ → isProp→isSet (isPropΠ λ _ → isPropΠ λ _ → isSetBElement Y _ _))
