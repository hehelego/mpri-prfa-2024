module common where

record Unit : Set where
  constructor unit

data Empty : Set where

absurd : {A : Set} → Empty → A
absurd ()

infix 3 ¬_
¬_ : Set → Set
¬ A = A → Empty

data Bool : Set where
  True  : Bool
  False : Bool

infixr 1 _⊎_
data _⊎_ (A B : Set) : Set where
  left  : (x : A) → A ⊎ B
  right : (y : B) → A ⊎ B

data Maybe (A : Set) : Set where
  Just : (a : A) → Maybe A
  Nothing : Maybe A

fmap : {A B : Set} (f : A → B) → Maybe A → Maybe B
fmap f (Just a) = Just (f a)
fmap f Nothing = Nothing

fmap2 : {A B C : Set} (f : A → B → C) → Maybe A → Maybe B → Maybe C
fmap2 f (Just a) (Just b) = Just (f a b)
fmap2 f _ Nothing = Nothing
fmap2 f Nothing _ = Nothing

IsJust : {A : Set} → Maybe A → Set
IsJust (Just _) = Unit
IsJust Nothing = Empty

fromJust : {A : Set} → (m : Maybe A) → IsJust m → A
fromJust (Just x) _ = x

infix 3 _⇔_
record _⇔_ (A B : Set) : Set where
  field
    ⇒ : A → B
    ⇐ : B → A

infix 4 ⟨_,_⟩
record Σ {A : Set} (B : A → Set) : Set where
  constructor ⟨_,_⟩
  field
    fst : A
    snd : B fst

infixr 2 _×_
_×_ : Set → Set → Set
A × B = Σ (λ (_ : A) → B)


infix 4 _≡_
data _≡_ {A : Set} : A → A → Set where
 refl : {x : A} → x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}

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

data Nat : Set where
  Z : Nat
  S : Nat → Nat

pred : Nat → Nat
pred Z = Z
pred (S n) = n

infixl 6 _+_
_+_ : Nat → Nat → Nat
Z + m = m
(S n) + m = S (n + m)

infixl 6 _-_
_-_ : Nat → Nat → Nat
Z - m = Z
S n - Z = S n
S n - S m = n - m

+-neutral-r : (n : Nat) → n + Z ≡ n
+-neutral-r Z = refl
+-neutral-r (S n) = cong S (+-neutral-r n)

+-suc-shift : {n m : Nat} → n + S m ≡ S (n + m)
+-suc-shift {Z} = refl
+-suc-shift {S n} = cong S +-suc-shift

+-comm : {n m : Nat} → n + m ≡ m + n
+-comm {n} {Z} = +-neutral-r n
+-comm {n} {S m} = trans +-suc-shift (cong S (+-comm {n} {m}))

n-n=Z : {n : Nat} → n - n ≡ Z
n-n=Z {Z} = refl
n-n=Z {S n} = n-n=Z {n}

minus-Z-r : {n : Nat} → n - Z ≡ n
minus-Z-r {Z} = refl
minus-Z-r {S n} = refl

minus-S : (n m : Nat) → n - S m ≡ pred (n - m)
minus-S Z Z = refl
minus-S Z (S m) = refl
minus-S (S n) Z = minus-Z-r
minus-S (S n) (S m) = minus-S n m

infix 4 _<_
data _<_ : Nat → Nat → Set where
  Z<S : {n : Nat} → Z < S n
  S<S : {n m : Nat} → n < m → S n < S m

<-unique : {n m : Nat} → (p q : n < m) → p ≡ q
<-unique Z<S Z<S = refl
<-unique (S<S p) (S<S q) = cong S<S (<-unique p q)

Sn<Sm→n<m : {n m : Nat} → S n < S m → n < m
Sn<Sm→n<m (S<S n<m) = n<m

n<Sn : {n : Nat} → n < S n
n<Sn {Z} = Z<S
n<Sn {S n} = S<S n<Sn

n<m→n<Sm : {n m : Nat} → n < m → n < S m
n<m→n<Sm Z<S = Z<S
n<m→n<Sm (S<S n<m) = S<S (n<m→n<Sm n<m)

Sn<m→n<m : {n m : Nat} → S n < m → n < m
Sn<m→n<m (S<S n<pred-m) = n<m→n<Sm n<pred-m

<-trans : {n m k : Nat} → n < m → m < k → n < k
<-trans Z<S (S<S m<k) = Z<S
<-trans (S<S n<m) (S<S m<k) = S<S (<-trans n<m m<k)

infix 4 _≤_
_≤_ : Nat → Nat → Set
n ≤ m = n < S m

n≤n : {n : Nat} → n ≤ n
n≤n = n<Sn

n<m→n≤m : {n m : Nat} → n < m → n ≤ m
n<m→n≤m Z<S = Z<S
n<m→n≤m (S<S n<m) = S<S (n<m→n≤m n<m)

add-monotone : {n m : Nat} → n < S (m + n)
add-monotone {n} {Z} = n<Sn
add-monotone {n} {S m} = n<m→n<Sm add-monotone

minus-monotone : {n m k : Nat} → n < m → n - k < m
minus-monotone {n} {m} {k} Z<S = Z<S
minus-monotone {n} {m} {Z} (S<S n<m) = S<S n<m
minus-monotone {S n} {S m} {S k} (S<S n<m) = minus-monotone (n<m→n<Sm n<m)

infixr 5 _∷_
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

length : {A : Set} → List A → Nat
length [] = Z
length (_ ∷ xs) = S (length xs)

[_] : {A : Set} → A → List A
[ x ] = x ∷ []

map : {A B : Set} (f : A → B) (xs : List A) → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

map-length : {A B : Set} {f : A → B} {xs : List A} → length (map f xs) ≡ length xs
map-length {xs = []} = refl
map-length {xs = x ∷ xs} = cong S map-length

infixr 5 _++_
_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

++-neutral-r : {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-neutral-r [] = refl
++-neutral-r (x ∷ xs) = cong (x ∷_) (++-neutral-r xs)

++-assoc : {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

++-length : {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
++-length [] ys = refl
++-length (x ∷ xs) ys = cong S (++-length xs ys)

data Any {A : Set} (P : A → Set) : List A → Set where
  here  : {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : {x : A} {xs : List A} (px : P x) (pxs : All P xs) → All P (x ∷ xs)
  
infix 4 _∈_
_∈_ : {A : Set} → A → List A → Set
_∈_ x = Any (x ≡_)

All-∈ : {A : Set} {P : A → Set} {xs : List A} {x : A}
      → All P xs
      → x ∈ xs
      → P x
All-∈ (px ∷ all) (here refl) = px
All-∈ (px ∷ all) (there mem) = All-∈ all mem

∈-map : {A B : Set} {f : A → B} {z : A} {xs : List A} → z ∈ xs → f z ∈ map f xs
∈-map (here refl) = here refl
∈-map (there z∈xs) = there (∈-map z∈xs)

infix 5 _!_
_!_ : {A : Set} → List A → Nat → Maybe A
[] ! n = Nothing
(x ∷ xs) ! Z = Just x
(x ∷ xs) ! S n = xs ! n

valid-index : {A : Set} (xs : List A) {n : Nat} (n<N : n < length xs) → IsJust (xs ! n)
valid-index (x ∷ xs) {Z} n<N = unit
valid-index (x ∷ xs) {S N} (S<S n<N) = valid-index xs n<N

mem→idx : {A : Set} {x : A} {xs : List A} → x ∈ xs → Σ (λ n → xs ! n ≡ Just x)
mem→idx (here refl) = ⟨ Z , refl ⟩
mem→idx {A} {x} {y ∷ xs} (there x∈xs) = let ⟨ idx , eq ⟩ = mem→idx x∈xs in ⟨ S idx , eq ⟩

idx→mem : {A : Set} {x : A} {xs : List A} → Σ (λ n → xs ! n ≡ Just x) → x ∈ xs
idx→mem {xs = x ∷ _} ⟨ Z , refl ⟩ = here refl
idx→mem {xs = x ∷ xs} ⟨ S idx , eq ⟩ = there (idx→mem ⟨ idx , eq ⟩)


infix 4 _⊆_
_⊆_ : {A : Set} → List A → List A → Set
_⊆_ {A} xs ys = {z : A} → z ∈ xs → z ∈ ys

∷-subset : {A : Set} {z : A} {xs ys : List A} → xs ⊆ ys → z ∷ xs ⊆ z ∷ ys
∷-subset {A} {z} xs⊆ys (here eq) = here eq
∷-subset {A} {z} xs⊆ys (there mem) = there (xs⊆ys mem)

++-subset-l : {A : Set} {xs ys : List A} → xs ⊆ xs ++ ys
++-subset-l {xs = []} = λ ()
++-subset-l {xs = x ∷ xs} = ∷-subset ++-subset-l

++-subset-r : {A : Set} {xs ys : List A} → ys ⊆ xs ++ ys
++-subset-r {xs = []} = λ y∈ys → y∈ys
++-subset-r {xs = x ∷ xs} = λ y∈ys → there (++-subset-r y∈ys)

∘-map : {A B C : Set} (f : A → B) (g : B → C) {xs : List A} → map (λ x → g (f x)) xs ≡ map g ((map f) xs)
∘-map f g {[]} = refl
∘-map f g {x ∷ xs} = cong ((g (f x)) ∷_) (∘-map f g)

map-ext : {A B : Set} (f g : A → B) (f=g : (x : A) → f x ≡ g x)
        → {xs : List A} → map f xs ≡ map g xs
map-ext f g f=g {[]} = refl
map-ext f g f=g {x ∷ xs} = cong2 _∷_ (f=g x) (map-ext f g f=g {xs})

map-id : {A : Set} {xs : List A} → map (λ x → x) xs ≡ xs
map-id {xs = []} = refl
map-id {xs = x ∷ xs} = cong (x ∷_) map-id

zip-map : {A B C : Set} (f : A → B → C) (xs : List A) (ys : List B) → List C
zip-map f [] ys = []
zip-map f (x ∷ xs) [] = []
zip-map f (x ∷ xs) (y ∷ ys) = f x y ∷ zip-map f xs ys

zip-map-idx : {A B C : Set} (f : A → B → C) (xs : List A) (ys : List B) (i : Nat)
            → (zip-map f xs ys ! i) ≡ fmap2 f (xs ! i) (ys ! i)
zip-map-idx f [] [] _ = refl
zip-map-idx f [] (x ∷ ys) Z = refl
zip-map-idx f [] (x ∷ ys) (S i) with ys ! i
... | Just _ = refl
... | Nothing = refl
zip-map-idx f (x ∷ xs) [] Z = refl
zip-map-idx f (x ∷ xs) [] (S i) with xs ! i
... | Just _ = refl
... | Nothing = refl
zip-map-idx f (x ∷ xs) (y ∷ ys) Z = refl
zip-map-idx f (x ∷ xs) (y ∷ ys) (S i) = zip-map-idx f xs ys i

reverse : {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ [ x ]

split-tail : {A : Set} {n : Nat} (xs : List A) (non-empty : length xs ≡ S n) → (Σ λ z → Σ λ ys → xs ≡ ys ++ [ z ])
split-tail (x ∷ []) refl = ⟨ x , ⟨ [] , refl ⟩ ⟩
split-tail (x ∷ y ∷ xs) refl = let ⟨ z , ⟨ ys , eq ⟩ ⟩ = split-tail (y ∷ xs) refl
                                in ⟨ z , ⟨ x ∷ ys , cong (x ∷_) eq ⟩ ⟩

rev-++ : {A : Set} (xs ys : List A) → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
rev-++ [] ys = sym (++-neutral-r (reverse ys))
rev-++ (x ∷ xs) ys = let IH = rev-++ xs ys
                         eq1 = cong (_++ [ x ]) IH
                         eq2 = ++-assoc (reverse ys) (reverse xs) [ x ]
                      in trans eq1 eq2

rev-inv : {A : Set} (xs : List A) → reverse (reverse xs) ≡ xs
rev-inv [] = refl
rev-inv (x ∷ xs) = let IH = rev-inv xs
                       eq1 = rev-++ (reverse xs) [ x ]
                       eq2 = cong (x ∷_) IH
                    in trans eq1 eq2


rev-len : {A : Set} (xs : List A) → length (reverse xs) ≡ length xs
rev-len [] = refl
rev-len (x ∷ xs) = let IH = rev-len xs
                       eq1 = ++-length (reverse xs) [ x ]
                       eq2 = +-suc-shift
                       eq3 = cong S (+-neutral-r (length (reverse xs)))
                       eq4 = cong S IH
                    in trans eq1 (trans eq2 (trans eq3 eq4))


-- enumerable finite set
-- isomorphic to {n : Nat | n < N}
postulate
    Fin : Nat → Set
    Fin→Nat : {N : Nat} (n : Fin N) → Σ λ n' → n' < N
    enumerate : (N : Nat) → List (Fin N)
    Nat→Fin : {N : Nat} (n : Fin N) → enumerate N ! Σ.fst (Fin→Nat n) ≡ Just n
    enum-size : (N : Nat) → length (enumerate N) ≡ N

Just-fromJust : {A : Set} (m : Maybe A) (j : IsJust m) → m ≡ Just (fromJust m j)
Just-fromJust (Just a) j = refl
