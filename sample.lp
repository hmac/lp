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

main : List Nat
main = tail Nat [Suc (Suc Zero), Suc Zero, Zero]
