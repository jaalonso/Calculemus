import tactic

class monoide_aditivo (M : Type) extends has_add M, has_zero M :=
(asociativa  : ∀ (x y z : M), (x + y) + z = x + (y + z))
(neutro_izq  : ∀ (x : M), 0 + x = x)
(neutro_dcha : ∀ (x : M), x + 0 = x)

namespace monoide_aditivo

instance : monoide_aditivo nat :=
{ add := (+),
  zero := 0,
  asociativa := add_assoc,
  neutro_izq := zero_add,
  neutro_dcha := add_zero }

end monoide_aditivo

class monoide_multiplicativo (M : Type) extends has_mul M, has_one M :=
(asociativa  : ∀ (x y z : M), (x * y) * z = x * (y * z))
(neutro_izq  : ∀ (x : M), 1 * x = x)
(neutro_dcha : ∀ (x : M), x * 1 = x)

namespace monoide_multiplicativo

instance : monoide_multiplicativo nat :=
{ mul := (*),
  one := 1,
  asociativa := mul_assoc,
  neutro_izq := one_mul,
  neutro_dcha := mul_one }

variable {α : Type}

instance : monoide_multiplicativo (α → α) :=
{ mul := (∘),
  one := id,
  asociativa := function.comp.assoc,
  neutro_izq := function.left_id,
  neutro_dcha := function.right_id }

end monoide_multiplicativo

@[class]
structure Monoide :=
  (M : Type*)
  (op : M → M → M) (infix *    := op)
  (e : M)          (notation 1 := e)
  (asociativa : ∀ (x y z : M), (x * y) * z = x * (y * z))
  (neutro_izq : ∀ (x : M), 1 * x = x)
  (neutro_dcha : ∀ (x : M), x * 1 = x)

class Monoide2 :=
  (M : Type*)
  (op : M → M → M) (infix *    := op)
  (e : M)          (notation 1 := e)
  (asociativa : ∀ (x y z : M), (x * y) * z = x * (y * z))
  (neutro_izq : ∀ (x : M), 1 * x = x)
  (neutro_dcha : ∀ (x : M), x * 1 = x)

structure Monoide' :=
  (M : Type*)
  (op : M → M → M) (infix *    := op)
  (id : M)         (notation 1 := id)
  (asociativa : ∀ (x y z : M), (x * y) * z = x * (y * z))
  (neutro_izq : ∀ (x : M), 1 * x = x)
  (neutro_dcha : ∀ (x : M), x * 1 = x)

def monoide_aditivo_naturales : Monoide :=
{ M := ℕ,
  op := (+),
  e := 0,
  asociativa := add_assoc,
  neutro_izq := zero_add,
  neutro_dcha := add_zero }

instance monoide_aditivo_naturales2 : Monoide :=
{ M := ℕ,
  op := (+),
  e := 0,
  asociativa := add_assoc,
  neutro_izq := zero_add,
  neutro_dcha := add_zero }

def monoide_multiplicativo_naturales : Monoide :=
{ M := ℕ,
  op := (*),
  e := 1,
  asociativa := mul_assoc,
  neutro_izq := one_mul,
  neutro_dcha := mul_one }

def monoide_multiplicativo_enteros : Monoide :=
{ M := ℤ,
  op := (*),
  e := 1,
  asociativa := mul_assoc,
  neutro_izq := one_mul,
  neutro_dcha := mul_one }

def monoide_endomorfismos (α : Type) : Monoide :=
{ M := α → α,
  op := (∘),
  e := id,
  asociativa := function.comp.assoc,
  neutro_izq := function.left_id,
  neutro_dcha := function.right_id }
