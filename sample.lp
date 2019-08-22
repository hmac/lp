inc : forall (n : Nat). Nat
inc = \n. natElim ((\n. Nat) : forall (n : Nat). Type) (Suc Zero) ((\k n. Suc n) : forall (k : Nat) (n : Nat). Nat) n

dec : forall (n : Nat). Nat
dec = \n. natElim ((\n. Nat) : forall (n : Nat). Type) Zero ((\k n. k) : forall (k : Nat) (n : Nat). Nat) n

plus : forall (n : Nat) (m : Nat). Nat
plus = \n m. natElim ((\n. Nat) : forall (n : Nat). Type) n ((\k n. Suc n) : forall (k : Nat) (n : Nat). Nat) m

minus : forall (n : Nat) (m : Nat). Nat
minus = \n m. natElim ((\n. Nat) : forall (n : Nat). Type) n ((\k n. dec n) : forall (k : Nat) (n : Nat). Nat) m

uncurry : forall (a : Type) (b : Type) (c : Type) (f : forall (x : a) (y : b). c) (p : a*b). c
uncurry = \a b c f p. prodElim f p

curry : forall (a : Type) (b : Type) (c : Type) (f : forall (p : a*b). c) (x : a) (y : b). c
curry = \a b c f x y. f (x*y)

length : forall (a : Type) (l : List a). Nat
length = \a l. listElim ((\l. Nat) : forall (l : List a). Type) l Zero ((\x xs acc. Suc acc) : forall (x : a) (xs : List a) (acc : Nat). Nat)

head : forall (a : Type) (default : a) (l : List a). a
head = \a def l. listElim ((\l. a) : forall (l : List a). Type) l def ((\x xs acc. x) : forall (x : a) (xs : List a) (acc : a). a)

tail : forall (a : Type) (l : List a). List a
tail = \a l. listElim ((\l. List a) : forall (l : List a). Type) l ([] : List a) ((\x xs acc. xs) : forall (x : a) (xs : List a) (acc : List a). List a)

map : forall (a : Type) (b : Type) (f : forall (x : a). b) (l : List a). List b
map = \a b f l. listElim ((\l. List b) : forall (l : List a). Type) l ([] : List b) ((\x xs acc. (f x)::acc) : forall (x : a) (xs : List a) (acc : List b). List b)

foldr : forall (a : Type) (b : Type) (f : forall (x : a) (acc : b). b) (e : b) (l : List a). b
foldr = \a b f e l. listElim ((\l. b) : forall (l : List a). Type) l e ((\x xs acc. f x acc) : forall (x : a) (xs : List a) (acc : b). b)

sum : forall (l : List Nat). Nat
sum = \l. foldr Nat Nat ((\x acc. plus x acc) : forall (x : Nat) (acc : Nat). Nat) Zero l

main : Nat
main = sum [Zero, Suc Zero, Suc (Suc Zero), Suc (Suc (Suc Zero))]
