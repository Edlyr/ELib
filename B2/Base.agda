{-# OPTIONS --cubical #-}

module ELib.B2.Base where

open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc ; elim to elimPropTrunc)
open import Cubical.HITs.SetTruncation renaming (rec to recSetTrunc ; elim to elimSetTrunc)
open import Cubical.Data.Sigma
--open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Embedding
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
PathP≡compPathR₀2 : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : y ≡ z) (q : ∥ x ≡ y ∥₀) (r : ∥ x ≡ z ∥₀) →
  (PathP (λ i → ∥ x ≡ p i ∥₀) q r) ≡ (q ≡ r ∙₀ ∣ sym p ∣₀)
PathP≡compPathR₀2 {x = x} {y = y} = J (λ z p → (q : ∥ x ≡ y ∥₀) (r : ∥ x ≡ z ∥₀) →
  (PathP (λ i → ∥ x ≡ p i ∥₀) q r) ≡ (q ≡ r ∙₀ ∣ sym p ∣₀)) λ q r → cong (λ x → q ≡ x) (rUnit₀ _)

PathP≡compPathR₀2refl : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : y ≡ x) (q : ∥ x ≡ y ∥₀) →
  (PathP (λ i → ∥ x ≡ p i ∥₀) q ∣ refl ∣₀) ≡ (q ≡ ∣ sym p ∣₀)
PathP≡compPathR₀2refl p q = PathP≡compPathR₀2 _ _ _ ∙ cong (λ x → q ≡ x) (sym (lUnit₀ _))

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


module retr {ℓ : Level} (Astruct : ConcreteAbelianGroup ℓ) where
  A = fst (fst Astruct)
  a = snd (fst Astruct)
  conn = fst (snd Astruct)
  simplConn = fst (snd (snd Astruct))
  2type = snd (snd (snd Astruct))
  
  Bstruct = B² (Aut² Astruct)
  B = fst (fst Bstruct)
  b = snd (fst Bstruct)
  connB = fst (snd Bstruct)
  simplConnB = fst (snd (snd Bstruct))
  2typeB = snd (snd (snd Bstruct))
  
  T : A → Type ℓ
  T a' = Σ[ α ∈ ∥ (a ≡ a) ≃ (a ≡ a') ∥₀ ] ((p : a ≡ a') → α ≡ (∣
    (λ q → q ∙ p) , compPathr-isEquiv p
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

  {-C : Type (ℓ-suc ℓ)
  C = Σ (Type ℓ) λ x → ∥ (a ≡ a) ≃ x ∥₀
  c : C
  c = ((a ≡ a) , ∣ idEquiv _ ∣₀)
  ϕ : A → C
  ϕ a' = (a ≡ a') , fst (fst (isContrT a'))

  isContrϕ⁻¹c : isContr (fiber ϕ c)
  isContrϕ⁻¹c = {!!} where
    --equiv1 : fiber ϕ c ≃ (Σ[ a' ∈ A ] Σ[ p ∈ (a ≡ a') ≃ (a ≡ a) ] PathP (λ i → ∥ (a ≡ a) ≃ p i ∥₀) (snd (ϕ a')) ∣ refl ∣₀)
    --equiv1 = isoToEquiv (iso (λ x → fst x , cong fst (snd x) , cong snd (snd x)) (λ y → fst y , ΣPathP (fst (snd y) , snd (snd y))) (λ _ → refl) λ _ → refl)
    equiv2 : fiber ϕ c ≃ (Σ[ a' ∈ A ] Σ[ f ∈ (a ≡ a) ≃ (a ≡ a') ] ∣ f ∣₀ ≡ snd (ϕ a'))
    equiv2 = isoToEquiv
      (iso
        (λ (a' , p) → a' , pathToEquiv (sym (cong fst p)) , {!!})
        {!!}
        {!!}
        {!!}
      )

  ϕ' : C ≃ B
  ϕ' = isoToEquiv (iso
    (λ x → fst x , recSetTrunc setTruncIsSet (λ eq → ∣ ua eq ∣₀) (snd x))
    (λ y → fst y , recSetTrunc setTruncIsSet (λ p → ∣ pathToEquiv p ∣₀) (snd y))
    (λ y → ΣPathP (refl , elimSetTrunc
      {B = λ α → recSetTrunc setTruncIsSet (λ eq → ∣ ua eq ∣₀) (recSetTrunc setTruncIsSet (λ p → ∣ pathToEquiv p ∣₀) α) ≡ α}
      (λ x → isProp→isSet (setTruncIsSet _ _)) (λ α → cong ∣_∣₀ (ua-pathToEquiv α)) (snd y)))
    λ x → ΣPathP (refl , elimSetTrunc
      {B = λ β → recSetTrunc setTruncIsSet (λ p → ∣ pathToEquiv p ∣₀) (recSetTrunc setTruncIsSet (λ eq → ∣ ua eq ∣₀) β) ≡ β}
      (λ x → isProp→isSet (setTruncIsSet _ _)) (λ β → cong ∣_∣₀ (pathToEquiv-ua β)) (snd x))) --

  pointed : fst ϕ' (ϕ a) ≡ b
  pointed = ΣPathP (refl , (recSetTrunc setTruncIsSet (λ eq → ∣ ua eq ∣₀) (fst (fst (isContrT a)))
         ≡⟨ cong (λ x → recSetTrunc setTruncIsSet (λ eq → ∣ ua eq ∣₀) (fst (fst (x))))
           (isPropIsContr (isContrT a) (isContrTa)) ⟩
       recSetTrunc setTruncIsSet (λ eq → ∣ ua eq ∣₀) (fst (fst (isContrTa)))
         ≡⟨ cong ∣_∣₀ uaIdEquiv ⟩
       _ ∎
      ))
  -}

  κ : (a' : A) → ∥ (a ≡ a) ≃ (a ≡ a') ∥₀
  κ = λ a' → fst (fst (isContrT a'))

  --ϕ' : A → Σ (Type ℓ) (λ x → ∥ (a ≡ a) ≃ x ∥₀)
  --ϕ' a' = (a ≡ a') , κ a'

  ϕ : A → B {- = Σ (Set ℓ) (λ x → ∥ (a ≡ a) ≡ x ∥₀) -}
  ϕ a' = (a ≡ a') , recSetTrunc setTruncIsSet (λ eq → ∣ ua eq ∣₀) (κ a')

  pointed : ϕ a ≡ b
  pointed = ΣPathP (refl ,
       (recSetTrunc setTruncIsSet (λ eq → ∣ ua eq ∣₀) (fst (fst (isContrT a)))
         ≡⟨ cong (λ x → recSetTrunc setTruncIsSet (λ eq → ∣ ua eq ∣₀) (fst (fst (x))))
           (isPropIsContr (isContrT a) (isContrTa)) ⟩
       recSetTrunc setTruncIsSet (λ eq → ∣ ua eq ∣₀) (fst (fst (isContrTa)))
         ≡⟨ cong ∣_∣₀ uaIdEquiv ⟩
       _ ∎
      ))

  pointedRetr : (A , a) →∙ (B , b)
  pointedRetr = ϕ , pointed

  isContrϕ⁻¹b : isContr (fiber ϕ b)
  isContrϕ⁻¹b = {!!} where --transport (cong isContr (sym (ua equiv2))) lemmaContr where
    {-equiv1 : fiber ϕ b ≃ (Σ[ a' ∈ A ] Σ[ p ∈ (a ≡ a') ≡ (a ≡ a) ] PathP (λ i → ∥ (a ≡ a) ≡ p i ∥₀) (snd (ϕ a')) ∣ refl ∣₀)
    equiv1 = isoToEquiv (iso (λ x → fst x , cong fst (snd x) , cong snd (snd x)) (λ y → fst y , ΣPathP (fst (snd y) , snd (snd y))) (λ _ → refl) λ _ → refl)

    equiv2 : fiber ϕ b ≃ (Σ[ a' ∈ A ] Σ[ f ∈ (a ≡ a) ≡ (a ≡ a') ] ∣ f ∣₀ ≡ snd (ϕ a'))
    equiv2 = compEquiv equiv1 (isoToEquiv
     (iso
      (λ (a' , p , !) → a' , sym p , sym (transport (PathP≡compPathR₀2refl _ _) !))
      (λ (a' , f) → a' , sym (fst f) , transport (sym (PathP≡compPathR₀2refl _ _)) (sym (snd f)))
      (λ x → ΣPathP (refl , ΣPathP (refl , setTruncIsSet _ _ _ _)))
      λ x → ΣPathP (refl , ΣPathP (refl , transport⁻Transport (PathP≡compPathR₀2refl _ _) _))
            -- Here, we could use the fact that we are in the double-(dependant)-loopspace of a set truncation,
            -- but transport-Transport works just fine without having to worry about dependant paths
     ))

    path→eq : (a' : A) → (p : (a ≡ a) ≡ (a ≡ a')) → (g : ∥ (a ≡ a) ≃ (a ≡ a') ∥₀) →
      ∣ p ∣₀ ≡ recSetTrunc setTruncIsSet (λ eq → ∣ ua eq ∣₀) g → ∣ pathToEquiv p ∣₀ ≡ g
    path→eq a' p g =
      elimSetTrunc {B = λ g → ∣ p ∣₀ ≡ recSetTrunc setTruncIsSet (λ eq → ∣ ua eq ∣₀) g → ∣ pathToEquiv p ∣₀ ≡ g}
        (λ _ → isProp→isSet (isPropΠ λ _ → setTruncIsSet _ _))
        (λ g q → recPropTrunc (setTruncIsSet _ _) (λ r → cong ∣_∣₀ (cong pathToEquiv r ∙ pathToEquiv-ua g)) ((transport (pathEqualityInTrunc0 _ _) q)))
        g

    eq→path : (a' : A) → (f : (a ≡ a) ≃ (a ≡ a')) → (g : ∥ (a ≡ a) ≃ (a ≡ a') ∥₀) →
      ∣ f ∣₀ ≡ g → ∣ ua f ∣₀ ≡ recSetTrunc setTruncIsSet (λ eq → ∣ ua eq ∣₀) g
    eq→path a' f g =
      elimSetTrunc {B = λ g → ∣ f ∣₀ ≡ g → ∣ ua f ∣₀ ≡ recSetTrunc setTruncIsSet (λ eq → ∣ ua eq ∣₀) g}
        (λ _ → isProp→isSet (isPropΠ λ _ → setTruncIsSet _ _))
        (λ g p → recPropTrunc (setTruncIsSet _ _) (λ q → cong (λ x → ∣ ua x ∣₀) q) (transport (pathEqualityInTrunc0 f g) p))
        g

    equiv3 : (Σ[ a' ∈ A ] Σ[ f ∈ (a ≡ a) ≡ (a ≡ a') ] ∣ f ∣₀ ≡ snd (ϕ a')) ≃ (Σ[ a' ∈ A ] Σ[ f ∈ (a ≡ a) ≃ (a ≡ a') ] ∣ f ∣₀ ≡ κ a')
    equiv3 = isoToEquiv
      (iso
        (λ (a' , p , !) → a' , pathToEquiv p , path→eq a' p (κ a') !)
        (λ (a' , f , !) → a' , ua f , eq→path a' f (κ a') !)
        (λ x → ΣPathP (refl , ΣPathP (pathToEquiv-ua _ , toPathP (setTruncIsSet _ _ _ _))))
        λ x → ΣPathP (refl , ΣPathP (ua-pathToEquiv _ , toPathP (setTruncIsSet _ _ _ _)))
      )-}

    caracκa : ∣ idEquiv (a ≡ a) ∣₀ ≡ κ a
    caracκa = sym (snd (fst caracTa (fst (isContrT a))))

    lemmaContr : isContr (Σ[ a' ∈ A ] Σ[ f ∈ (a ≡ a) ≃ (a ≡ a') ] ∣ f ∣₀ ≡ κ a')
    lemmaContr = (a , idEquiv (a ≡ a) , caracκa) , contr where
      contr : (y : Σ[ a' ∈ A ] Σ[ f ∈ (a ≡ a) ≃ (a ≡ a') ] ∣ f ∣₀ ≡ κ a') → (a , idEquiv (a ≡ a) , caracκa) ≡ y
      contr (a' , f , !) = ΣPathP (fst f refl , toPathP (ΣPathP (lemmaTransp ∙ {!!} , toPathP (setTruncIsSet _ _ _ _)))) where
        transport→R : {X Y Z : Type ℓ} (p : Y ≡ Z) (f : X → Y) →
          transport (λ i → X → (p i)) f ≡ λ x → transport p (f x)
        transport→R {X} {Y} {Z} p f = J (λ Z p → transport (λ i → X → (p i)) f ≡ λ x → transport p (f x))
          (funExt λ x → cong (λ f → f x) (transportRefl f) ∙ sym (transportRefl (f x))) p
          
        concLeft : (a ≡ a) ≃ (a ≡ a')
        concLeft = (λ q → q ∙ fst f refl) , compPathr-isEquiv _

        lemmaTransp : (transport (λ i → (a ≡ a) ≃ (a ≡ fst f refl i)) (idEquiv _)) ≡ concLeft
        lemmaTransp = equivEq _ _ (transport (λ i → (a ≡ a) → (a ≡ fst f refl i)) (λ x → x)
         ≡⟨ (funExt λ q → cong (λ f → f q) (transport→R (λ i → a ≡ fst f refl i) (λ x → x)) ∙ fromPathP {A = λ i → a ≡ fst f refl i}
            (transport (sym (PathP≡compPathR _ _ _)) refl)) ⟩
         _ ∎)

        test : Type (ℓ-suc ℓ)
        test = Σ (Type ℓ) λ x → ∥ (a ≡ a) ≃ x ∥₀

        x₀ : test
        x₀ = (a ≡ a) , ∣ idEquiv (a ≡ a) ∣₀
        x₁ : test
        x₁ = (a ≡ a') , κ a'

        ok : {X Y : Type ℓ} (p : X ≡ Y) → transport (λ i → ∥ X ≃ p i ∥₀) (∣ idEquiv _ ∣₀) ≡ ∣ pathToEquiv p ∣₀
        ok {X} = J (λ Y p → transport (λ i → ∥ X ≃ p i ∥₀) (∣ idEquiv _ ∣₀) ≡ ∣ pathToEquiv p ∣₀)
          (transportRefl ∣ idEquiv X ∣₀ ∙ cong ∣_∣₀ (sym pathToEquivRefl))

        p₁ : x₀ ≡ x₁
        p₁ = ΣPathP (ua f , toPathP (ok (ua f) ∙ cong ∣_∣₀ (pathToEquiv-ua f) ∙ !))
        p₂ : x₀ ≡ x₁
        p₂ = ΣPathP (ua concLeft , toPathP (ok (ua concLeft) ∙ cong ∣_∣₀ (pathToEquiv-ua concLeft) ∙ sym (snd (fst (isContrT a')) (fst f refl))))
    {-lemmaContr : isContr (Σ[ a' ∈ A ] Σ[ f ∈ (a ≡ a) ≡ (a ≡ a') ] ∣ f ∣₀ ≡ snd (ϕ a'))
    lemmaContr = (a , refl , sym (cong snd pointed)) , contr where
      contr : (y : Σ-syntax A (λ a' →  Σ-syntax ((a ≡ a) ≡ (a ≡ a')) (λ f → ∣ f ∣₀ ≡ snd (ϕ a')))) → (a , (λ _ → a ≡ a) , (λ i → snd (pointed (~ i)))) ≡ y
      contr (a' , f , !) = ΣPathP (fst (pathToEquiv f) refl , toPathP (ΣPathP (finalLemma , toPathP (setTruncIsSet _ _ _ _)))) where
        subLemma : (p : a ≡ a') → transport (λ i → (a ≡ a) ≡ (a ≡ p i)) refl ≡ (λ i → (a ≡ p i))
        subLemma = J (λ a' p → transport (λ i → (a ≡ a) ≡ (a ≡ p i)) refl ≡ (λ i → (a ≡ p i))) (transportRefl _)
        
        eq1 : (((a ≡ a) , ∣ refl ∣₀) ≡ (pointed i1)) ≃ (a ≡ a)
        eq1 = (sec (Aut² Astruct))

        eq2 : (((a ≡ a) , ∣ refl ∣₀) ≡ (pointed i1)) ≃ (a ≡ a)
        eq2 = fun , transport (cong isEquiv (funExt λ x → transportRefl _ ∙ cong (transport (cong fst x)) (transportRefl _))) (snd eq1) where
          fun : (((a ≡ a) , ∣ refl ∣₀) ≡ (pointed i1)) → (a ≡ a)
          fun x = transport (cong fst x) refl

        ∙pointed : (pointed i1 ≡ pointed i0) ≃ (pointed i1 ≡ pointed i1)
        ∙pointed = isoToEquiv (iso
          (λ x → x ∙ pointed)
          (λ y → y ∙ sym pointed)
          (λ y → sym (assoc _ _ _) ∙ cong (λ x → y ∙ x) (lCancel pointed) ∙ (sym (rUnit y)))
          λ x → sym (assoc _ _ _) ∙ (λ i → x ∙ (rCancel pointed i)) ∙ sym (rUnit x))
          -- For an unknown reason, using "cong" instead of "λ i → ..." in the above line results in a compiling timeout :
          -- λ x → sym (assoc _ _ _) ∙ (cong (λ y → x ∙ y) (rCancel pointedBis)) ∙ sym (rUnit x)
 
        eq3 : (pointed i1 ≡ pointed i0) ≃ (a ≡ a)
        eq3 = compEquiv ∙pointed eq2

        ev-_-reflₐ : (a' : A) → b ≡ (ϕ a') → (a ≡ a')
        ev-_-reflₐ a' p = (transport (cong fst p)) refl

        truc : ev- a -reflₐ ≡ fst eq3
        truc = funExt λ x → _ ≡⟨ cong (ev- a -reflₐ) (rUnit x) ⟩ ev- a -reflₐ (x ∙ refl) ∎
        
        ev-a'-eq : (a' : A) → isEquiv ev- a' -reflₐ
        ev-a'-eq a' = recPropTrunc (isPropIsEquiv _) (λ a≡a' → transport (cong (λ x → isEquiv ev- x -reflₐ) a≡a')
          (transport (cong isEquiv (sym truc)) (snd eq3))) (conn a a')

        wesh1 : b ≡ (ϕ a')
        wesh1 = ΣPathP (f , symP {A = λ i → ∥ (a ≡ a) ≡ f (~ i) ∥₀} (transport (sym (PathP≡compPathR₀2refl _ _)) (sym !)))

        wesh2 : b ≡ (ϕ a')
        wesh2 = ΣPathP (((λ i → a ≡ transport f refl i)) , {!!})

        ok : (ev- a' -reflₐ wesh1) ≡ (ev- a' -reflₐ wesh2)
        ok = transport f refl ≡⟨ sym (fromPathP {A = λ i → a ≡ transport f refl i}
          (transport (sym (PathP≡compPathR _ _ _)) (sym (lUnit _)))) ⟩ transport (λ i → a ≡ transport f refl i) refl ∎

        finalLemma : transport (λ i → (a ≡ a) ≡ (a ≡ transport f refl i)) (λ _ → a ≡ a) ≡ f
        finalLemma = subLemma (transport f refl) ∙ sym (cong (cong fst) (fst (invEquiv (_ , isEquiv→isEmbedding (ev-a'-eq a') wesh1 wesh2)) ok))
  -}
  ϕeq : isEquiv ϕ
  ϕeq .equiv-proof y = recPropTrunc isPropIsContr (λ p → transport (cong (λ x → isContr (fiber ϕ x)) p) isContrϕ⁻¹b) (connB b y) where

  equivRetr : A ≃ B
  equivRetr = ϕ , ϕeq

--retrFun : ∀ {ℓ} (A : ConcreteAbelianGroup ℓ) → (fst A) →∙ (fst (B² (Aut² A)))
--retrFun {ℓ} A = retr.pointedRetr A

--retrEq : ∀ {ℓ} (A : ConcreteAbelianGroup ℓ) → fst (fst A) ≃ fst (fst (B² (Aut² A)))
--retrEq A = retr.equivRetr A
