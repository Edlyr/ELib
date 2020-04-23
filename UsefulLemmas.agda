{-# OPTIONS --cubical #-}

module ELib.UsefulLemmas where

open import Cubical.Foundations.Everything
open import Cubical.Homotopy.Loopspace -- for Eckmann-Hilton
open import Cubical.Data.Sigma

typeof : ∀ {ℓ} {A : Type ℓ} → A → Type ℓ
typeof {ℓ} {A} a = A

-- Multi-level definition of Unit
data Unit {ℓ} : Type ℓ where
  tt : Unit

isContrUnit : ∀ {ℓ} → isContr (Unit {ℓ})
isContrUnit = tt , λ {tt → refl}

-- Transport in path spaces
PathP≡compPathR : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) (r : x ≡ z)
  → (PathP (λ i → x ≡ q i) p r) ≡ (p ∙ q ≡ r)
PathP≡compPathR p q r k = PathP (λ i → p i0 ≡ q (i ∨ k)) (λ j → compPath-filler p q k j) r

PathP≡compPathL : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) (r : x ≡ z)
  → (PathP (λ i → p i ≡ z) r q) ≡ (p ⁻¹ ∙ r ≡ q)
PathP≡compPathL p q r = _ ≡⟨ PathP≡doubleCompPathˡ p r q refl ⟩ cong (λ x → x ≡ q) (sym (compPath≡compPath' _ _))

-- Path simplification
p∙q⁻¹≡refl→p≡q : ∀ {ℓ} {A : Type ℓ} {a b : A} (p q : a ≡ b) → (p ∙ q ⁻¹) ≡ refl → p ≡ q
p∙q⁻¹≡refl→p≡q p q r = rUnit _ ∙ (cong (λ x → p ∙ x) (sym (lCancel q))) ∙ assoc _ _ _ ∙ cong (λ x → x ∙ q) r ∙ sym (lUnit _)

p≡q→p∙q⁻¹≡refl : ∀ {ℓ} {A : Type ℓ} {a b : A} (p q : a ≡ b) → p ≡ q → (p ∙ q ⁻¹) ≡ refl
p≡q→p∙q⁻¹≡refl p q r = cong (λ x → x ∙ q ⁻¹)  r ∙ (rCancel _)

-- Eckmann-Hilton property
preEckmann-Hilton : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p q : x ≡ y) (r s : y ≡ z) (g : p ≡ q) (h : r ≡ s) →
  (cong (λ t → t ∙ r) g) ∙ (cong (λ t → q ∙ t) h) ≡ (cong (λ t → p ∙ t) h) ∙ (cong (λ t → t ∙ s) g)
preEckmann-Hilton p q r s g h = J (λ s h → (cong (λ t → t ∙ r) g) ∙ (cong (λ t → q ∙ t) h) ≡ (cong (λ t → p ∙ t) h) ∙ (cong (λ t → t ∙ s) g))
  (sym (rUnit _) ∙ lUnit _) h

Eckmann-Hilton : ∀ {ℓ} (A : Pointed ℓ) (g h : (fst ((Ω^ 2) A))) → g ∙ h ≡ h ∙ g
Eckmann-Hilton A g h = transport (λ i → PathP (λ j → simplification i j) (g ∙ h) (h ∙ g)) finalPath where
  r = rUnit (snd (Ω A))
  x : (r i0 ≡ r i0) ≡ (r i1 ≡ r i1)
  x = (λ i → r i ≡ r i)
  simplification : x ∙ refl ∙ (sym x) ≡ refl
  simplification = (cong (λ y → x ∙ y) (sym (lUnit _))) ∙ rCancel x

  preEck = preEckmann-Hilton refl refl refl refl g h
  path1 : PathP (λ i → r i ≡ r i) (g ∙ h) (cong (λ t → t ∙ (λ _ → snd A)) g ∙ cong (_∙_ (λ _ → snd A)) h)
  path1 i j = hcomp (λ k → λ {(j = i0) → r i ; (j = i1) → lUnit (h k) i}) (rUnit (g j) i)
  path2 : PathP (λ i → r i ≡ r i) (h ∙ g) (cong (_∙_ (λ _ → snd A)) h ∙ cong (λ t → t ∙ (λ _ → snd A)) g)
  path2 i j = hcomp (λ k → λ {(j = i0) → r i ; (j = i1) → rUnit (g k) i}) (lUnit (h j) i)
  finalPath : PathP (λ j → (x ∙ refl ∙ sym x) j) (g ∙ h) (h ∙ g)
  finalPath = (compPathP path1 (compPathP preEck (symP path2)))
