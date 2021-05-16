theory reto_sol2
imports Main
begin

lemma
  fixes f :: "bool \<Rightarrow> bool"
  shows "f (f (f b)) = f b"
  by (cases b; cases "f True"; cases "f False"; simp)

end