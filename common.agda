module common where

infixr 5 _∷_
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

data _≡_ {A : Set} : A → A → Set where
  refl : {x : A} → x ≡ x

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

cong : {A B : Set} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

cong2 : {A B C : Set} {x x' : A} {y y' : B} (f : A → B → C) → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
cong2 f refl refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

subst : {A : Set} (P : A → Set) {x y : A} → P x → x ≡ y → P y
subst P px refl = px

subst2 : {A B : Set} (P : A → B → Set) {x x' : A} {y y' : B} → P x y → x ≡ x' → y ≡ y' → P x' y'
subst2 P pxy refl refl = pxy

data Any {A : Set} (P : A → Set) : List A → Set where
  here  : {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : {x : A} {xs : List A} (px : P x) (pxs : All P xs) → All P (x ∷ xs)

data ℕ : Set where
  Z : ℕ
  S : ℕ → ℕ

infix 4 _∈_
_∈_ : {A : Set} → A → List A → Set
_∈_ x = Any (x ≡_)

infix 4 _⊆_
_⊆_ : {A : Set} → List A → List A → Set
_⊆_ {A} xs ys = {z : A} → z ∈ xs → z ∈ ys

∷-subset : {A : Set} {z : A} {xs ys : List A} → xs ⊆ ys → z ∷ xs ⊆ z ∷ ys
∷-subset {A} {z} xs⊆ys (here eq) = here eq
∷-subset {A} {z} xs⊆ys (there mem) = there (xs⊆ys mem)

data ∅ : Set where

infix 4 ¬_
¬_ : Set → Set
¬ A = A → ∅

record _⇔_ (A B : Set) : Set where
  field
    ⇒ : A → B
    ⇐ : B → A

map : {A B : Set} (f : A → B) (xs : List A) → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

∈-map : {A B : Set} {f : A → B} {z : A} {xs : List A} → z ∈ xs → f z ∈ map f xs
∈-map (here refl) = here refl
∈-map (there z∈xs) = there (∈-map z∈xs)

infixr 15 _⊎_
data _⊎_ (A B : Set) : Set where
  left  : (x : A) → A ⊎ B
  right : (y : B) → A ⊎ B

record Σ {A : Set} (B : A → Set) : Set where
  constructor ⟨_,_⟩
  field
    fst : A
    snd : B fst

infixr 15 _×_
_×_ : Set → Set → Set
A × B = Σ (λ (_ : A) → B)

infix 10 _!_≔_
data _!_≔_ {A : Set} : List A → ℕ → A → Set where
  at-Z : {x : A} {xs : List A} → (x ∷ xs) ! Z ≔ x
  at-S : {x y : A} {xs : List A} {n : ℕ} → xs ! n ≔ x → (y ∷ xs) ! (S n) ≔ x

mem→idx : {A : Set} {x : A} {xs : List A} → x ∈ xs → Σ (λ n → xs ! n ≔ x)
mem→idx (here refl) = ⟨ Z , at-Z ⟩
mem→idx {A} {x} {y ∷ xs} (there x∈xs) = let ⟨ n , at-n ⟩ = mem→idx x∈xs
                                         in ⟨ S n , at-S at-n ⟩

idx→mem : {A : Set} {x : A} {xs : List A} → Σ (λ n → xs ! n ≔ x) → x ∈ xs
idx→mem ⟨ Z , at-Z ⟩ = here refl
idx→mem ⟨ S n , at-S at-n ⟩ = let x∈xs = idx→mem ⟨ n , at-n ⟩
                               in there x∈xs

data 𝔹 : Set where
  True  : 𝔹
  False : 𝔹
