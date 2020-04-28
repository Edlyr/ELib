{-# OPTIONS --cubical #-}

module ELib.B2.Base where

open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc ; elim to elimPropTrunc)
open import Cubical.HITs.SetTruncation renaming (rec to recSetTrunc ; elim to elimSetTrunc)
open import Cubical.Data.Sigma
--open import Cubical.Functions.FunExtEquiv
--open import Cubical.Functions.Embedding
open import ELib.Connectedness.Base
open import ELib.Connectedness.Properties
open import ELib.ConcreteGroup.Base
--open import Cubical.Homotopy.Loopspace
open import ELib.UniversalCover.Base
open import ELib.UsefulLemmas

ConcreteAbelianGroup : ∀ ℓ → Type (ℓ-suc ℓ)
ConcreteAbelianGroup ℓ = Σ[ A ∈ Pointed ℓ ] isConnected(fst A) × isConnected(snd A ≡ snd A) × is2Groupoid (fst A)

{- Definition of B² with equality between pointed types
B² : ∀ {ℓ} → AbConcreteGroup ℓ → ConcreteAbelianGroup (ℓ-suc ℓ)
B² {ℓ} (G , abG) =
  B ,
  isConnectedUniversalCover A ,
  isSimplyConnectedUniversalCover A ,
  2groupoid
  where
  open ConcreteGroup G
  A : Pointed (ℓ-suc ℓ)
  A = (Pointed ℓ) , Ptd
  B : Pointed (ℓ-suc ℓ)
  B = UniversalCover A
  connUC = isConnectedUniversalCover A
  2groupoid : is2Groupoid (fst B)
  2groupoid x y =
    recPropTrunc isPropIsGroupoid  (λ px →
    recPropTrunc isPropIsGroupoid (λ py →
      transport (λ i → isGroupoid (px i ≡ py i))
        (transport (cong isGroupoid (ua Σ≡))
          (isGroupoidΣ (transport (cong isGroupoid (ua Σ≡))
            (isGroupoidΣ (isOfHLevel≡ 3 isGrpd isGrpd)
            λ _ → isSet→isGroupoid (transport (cong isSet (sym (PathP≡Path _ _ _))) (isGrpd _ _))))
          λ p → transport (cong isGroupoid (sym (PathP≡Path _ _ _))) (isSet→isGroupoid (isProp→isSet (setTruncIsSet _ _))))
        )
    ) (connUC (snd B) y))
    (connUC (snd B) x)
-}

B² : ∀ {ℓ} → AbConcreteGroup ℓ → ConcreteAbelianGroup (ℓ-suc ℓ)
B² {ℓ} (G , abG) =
  B ,
  isConnectedUniversalCover A ,
  isSimplyConnectedUniversalCover A ,
  2groupoid
  where
  open ConcreteGroup G
  A : Pointed (ℓ-suc ℓ)
  A = (Type ℓ) , type
  B : Pointed (ℓ-suc ℓ)
  B = UniversalCover A
  connUC = isConnectedUniversalCover A
  2groupoid : is2Groupoid (fst B)
  2groupoid x y =
    recPropTrunc isPropIsGroupoid  (λ px →
    recPropTrunc isPropIsGroupoid (λ py →
      transport (λ i → isGroupoid (px i ≡ py i))
        (transport (cong isGroupoid (ua Σ≡)) (isGroupoidΣ (isOfHLevel≡ 3 isGrpd isGrpd)
        λ _ → isSet→isGroupoid (isProp→isSet (transport (cong isProp (sym (PathP≡Path _ _ _))) (setTruncIsSet _ _)))))
    ) (connUC (snd B) y))
    (connUC (snd B) x)

Aut² : ∀ {ℓ} → ConcreteAbelianGroup ℓ → AbConcreteGroup ℓ
Aut² {ℓ} ((A , a) , conn , simplConn , 2type) =
  conc-group
    BG
    (struct-conc-group
      pnt
      (simplConn pnt)
      (2type _ _ _ _)
    ) ,
  Eckmann-Hilton (A , a)
  where
  BG : Type ℓ
  BG = a ≡ a
  pnt : BG
  pnt = refl

PathP≡compPathR₀ : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : y ≡ z) (q : ∥ x ≡ y ∥₀) (r : ∥ x ≡ z ∥₀) →
  (PathP (λ i → ∥ x ≡ p i ∥₀) q r) ≡ (q ∙₀ ∣ p ∣₀ ≡ r)
PathP≡compPathR₀ {x = x} {y = y} p =
  J
    (λ z p →  (q : ∥ x ≡ y ∥₀) (r : ∥ x ≡ z ∥₀) → (PathP (λ i → ∥ x ≡ p i ∥₀) q r) ≡ (q ∙₀ ∣ p ∣₀ ≡ r))
    (λ q r → cong (λ x → x ≡ r) (rUnit₀ q))
    p

sec : ∀ {ℓ} (G : AbConcreteGroup ℓ) → ConcreteGroup.type (fst (Aut² (B² G))) ≃ ConcreteGroup.type (fst G)
sec (G , ab) =
  (type , ∣ refl ∣₀) ≡ (type , ∣ refl ∣₀)
    ≃⟨ invEquiv Σ≡ ⟩
  Σ[ p ∈ type ≡ type ] PathP (λ i → ∥ type ≡ p i ∥₀) ∣ refl ∣₀ ∣ refl ∣₀
    ≃⟨ pathToEquiv (cong (Σ (type ≡ type)) (funExt λ p →
      PathP (λ i → ∥ type ≡ p i ∥₀) ∣ refl ∣₀ ∣ refl ∣₀
        ≡⟨ PathP≡compPathR₀ _ _ _ ∙ cong (λ x → x ≡ ∣ refl ∣₀) (sym (lUnit₀ _)) ⟩
      ∣ p ∣₀ ≡ ∣ refl ∣₀
        ≡⟨ pathEqualityInTrunc0 _ _ ⟩
      ∥ p ≡ refl ∥ ∎
    )) ⟩
  Σ[ p ∈ type ≡ type ] ∥ p ≡ refl ∥
    ≃⟨ BZ'≃BZ G ⟩
  ConcreteGroup.type (Z G)
    ≃⟨ (_ , isAbelian→isAbelian' G ab) ⟩
  type ■
  where
  open ConcreteGroup G

secPnt : ∀ {ℓ} (G : AbConcreteGroup ℓ) → (fst (sec G) (ConcreteGroup.pnt (fst (Aut² (B² G)))) ≡ ConcreteGroup.pnt (fst G))
secPnt G = transportRefl _ ∙ transportRefl _ ∙ transportRefl _


module retr {ℓ : Level} (((A , a) , conn , simplConn , 2type) : ConcreteAbelianGroup ℓ) where
  T : A → Type ℓ
  T a' = Σ[ α ∈ ∥ (a ≡ a) ≃ (a ≡ a') ∥₀ ] ((p : a ≡ a') → α ≡ (∣
    isoToEquiv (iso (λ q → q ∙ p) (λ r → r ∙ p ⁻¹)
      (λ r → sym (assoc _ _ _) ∙ (cong (λ x → r ∙ x) (lCancel _)) ∙ sym (rUnit _))
      λ q → sym (assoc _ _ _) ∙ (cong (λ x → q ∙ x) (lCancel _)) ∙ sym (rUnit _) )
   ∣₀))
  caracTa : T a ≃ (Σ[ α ∈ ∥ (a ≡ a) ≃ (a ≡ a) ∥₀ ] (α ≡ ∣ idEquiv _ ∣₀))
  caracTa = isoToEquiv
   (iso
    (λ x → fst x , snd x refl ∙ cong ∣_∣₀ (equivEq _ _ (funExt λ q → sym (rUnit q))))
    (λ y → fst y , λ p → recPropTrunc (setTruncIsSet _ _) (λ pConnec →
      snd y ∙ cong ∣_∣₀ (equivEq _ _ (funExt λ r → rUnit r ∙ cong (λ x → r ∙ x) pConnec))) (simplConn refl p))
    (λ y → ΣPathP (refl , setTruncIsSet _ _ _ _))
    (λ x → ΣPathP (refl , funExt λ _ → setTruncIsSet _ _ _ _))
   )
  isContrTa : isContr (T a)
  isContrTa =
    transport (cong isContr (sym (ua (
      _
        ≃⟨ caracTa ⟩
      Σ[ α ∈ ∥ (a ≡ a) ≃ (a ≡ a) ∥₀ ] (α ≡ ∣ idEquiv _ ∣₀)
        ≃⟨ isoToEquiv (iso (λ _ → tt) (λ {tt → ∣ idEquiv _ ∣₀ , refl})
          (λ {tt → refl}) λ x → ΣPathP (sym (snd x) , toPathP (setTruncIsSet _ _ _ _))) ⟩
      Unit ■
    )))) isContrUnit
  isContrT : (a' : A) → isContr (T a')
  isContrT a' = recPropTrunc isPropIsContr (λ p →
    transport (cong (λ x → isContr (T x)) p) isContrTa) (conn a a')

  ϕ : A → Σ (Set ℓ) (λ x → ∥ (a ≡ a) ≡ x ∥₀)
  ϕ a' = (a ≡ a') , recSetTrunc setTruncIsSet (λ eq → ∣ ua eq ∣₀) (fst (fst (isContrT a')))

  Astruct : ConcreteAbelianGroup ℓ
  Astruct = ((A , a) , conn , simplConn , 2type)
  pointed : ϕ a ≡ snd (fst (B² (Aut² Astruct)))
  pointed = ΣPathP (refl , (
    recSetTrunc setTruncIsSet (λ eq → ∣ ua eq ∣₀) (fst (fst (isContrT a)))
      ≡⟨ cong (λ x → recSetTrunc setTruncIsSet (λ eq → ∣ ua eq ∣₀) (fst (fst (x))))
        (isPropIsContr (isContrT a) (isContrTa)) ⟩
    recSetTrunc setTruncIsSet (λ eq → ∣ ua eq ∣₀) (fst (fst (isContrTa)))
      ≡⟨ cong ∣_∣₀ uaIdEquiv ⟩
    _ ∎
   ))

  pointedRetr : (A , a) →∙ fst (B² (Aut² Astruct))
  pointedRetr = ϕ , pointed

  ϕeq : isEquiv ϕ
  ϕeq = {!!}

  equivRetr : A ≃ fst (fst (B² (Aut² Astruct)))
  equivRetr = ϕ , ϕeq

retrFun : ∀ {ℓ} (A : ConcreteAbelianGroup ℓ) → (fst A) →∙ (fst (B² (Aut² A)))
retrFun {ℓ} A = retr.pointedRetr A

retrEq : ∀ {ℓ} (A : ConcreteAbelianGroup ℓ) → fst (fst A) ≃ fst (fst (B² (Aut² A)))
retrEq A = retr.equivRetr A
