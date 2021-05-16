theory reto_sol1
imports Main
begin

lemma 
  fixes f :: "bool \<Rightarrow> bool"
  shows "f (f (f b)) = f b"
  by smt

end