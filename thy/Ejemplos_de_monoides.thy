theory Ejemplos_de_monoides
imports Main HOL.Real
begin

class Monoide = 
  fixes op :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "**" 70)
    and e  :: 'a 
  assumes 
        asociativa: "(x ** y) ** z = x ** (y ** z)"
    and neutro_izq: "e ** x = x"
    and neutro_cha: "x ** e = x"

(*
instantiation nat :: Monoide
begin

definition 
  op_nat_def [simp] : "i ** j = i + (j :: nat)"

definition
  e_nat_def [simp] : "e \<equiv> (0 :: nat)"

instance
proof
  fix x y z :: nat
  show "(x ** y) ** z = x ** (y ** z)" 
    by simp
next
  fix x :: nat
  show "e ** x = x"
    by simp
next
  fix x :: nat
  show "x ** e = x" 
    by simp
qed

end
*)

instantiation nat :: Monoide
begin

definition 
  op_nat_def [simp] : "i ** j = i + (j :: nat)"

definition
  e_nat_def [simp] : "e \<equiv> (0 :: nat)"

instance by standard simp_all

end

end