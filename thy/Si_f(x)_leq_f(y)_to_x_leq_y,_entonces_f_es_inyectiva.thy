(* Si_f(x)_leq_f(y)_to_x_leq_y,_entonces_f_es_inyectiva.thy
-- Si `f x \<le> f y \<rightarrow> x \<le> y`, entonces f es inyectiva
-- José A. Alonso Jiménez
-- Sevilla, 22 de julio de 2021
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Sea f una función de \<real> en \<real> tal que
--    \<forall> x y, f(x) \<le> f(y) \<rightarrow> x \<le> y
-- Demostrar que f es inyectiva.
-- ------------------------------------------------------------------ *)

theory "Si_f(x)_leq_f(y)_to_x_leq_y,_entonces_f_es_inyectiva"
imports Main HOL.Real
begin

(* 1\<ordfeminine> demostración *)
lemma
  fixes f :: "real \<Rightarrow> real"
  assumes "\<forall> x y. f x \<le> f y \<longrightarrow> x \<le> y"
  shows   "inj f"
proof (rule injI)
  fix x y
  assume "f x = f y"
  show "x = y"
  proof (rule antisym)
    show "x \<le> y"
      by (simp only: assms \<open>f x = f y\<close>)
  next
    show "y \<le> x"
      by (simp only: assms \<open>f x = f y\<close>)
  qed
qed

(* 2\<ordfeminine> demostración *)
lemma
  fixes f :: "real \<Rightarrow> real"
  assumes "\<forall> x y. f x \<le> f y \<longrightarrow> x \<le> y"
  shows   "inj f"
proof (rule injI)
  fix x y
  assume "f x = f y"
  then show "x = y"
    using assms
    by (simp add: eq_iff)
qed

(* 3\<ordfeminine> demostración *)
lemma
  fixes f :: "real \<Rightarrow> real"
  assumes "\<forall> x y. f x \<le> f y \<longrightarrow> x \<le> y"
  shows   "inj f"
  by (smt (verit, ccfv_threshold) assms inj_on_def)

end
