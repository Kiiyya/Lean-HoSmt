inductive Vec (α : Type) : Nat -> Type where
| nil  :                             Vec α Nat.zero
| cons : (_ : α) -> (_ : Vec α n) -> Vec α (Nat.succ n)
  infixr:67 " :: " => Vec.cons
  notation "[]" => Vec.nil

def length : Vec α n -> Nat
| .nil => .zero
| .cons _ v' => .succ <| length v'

def sum : Vec Nat n -> Nat
| [] => 0
| x :: xs => x + (sum xs)

def max : Vec Nat n -> Nat
| [] => 0
| x :: xs => if x > max xs then x else max xs

def map (f : α -> α) : Vec α n -> Vec α n
| [] => []
| x :: xs => (f x) :: (map f xs)

def get {α : Type} : Vec α n -> Fin n -> α
| .nil      , ⟨k      , h⟩ => absurd h (Nat.not_lt_zero k)
| .cons _ xs, ⟨.succ k, h⟩ => get xs ⟨k, Nat.lt_of_succ_lt_succ h⟩
| .cons x  _, ⟨.zero  , h⟩ => x

def get! [Inhabited α] : Vec α n -> Nat -> α
| .nil      , _         => panic! ""
| .cons x  _, .zero     => x
| .cons _ xs, (.succ k) => get! xs k
