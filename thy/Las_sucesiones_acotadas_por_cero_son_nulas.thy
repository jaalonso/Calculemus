(* Las_sucesiones_acotadas_por_cero_son_nulas.thy
-- Las sucesiones acotadas por cero son nulas
-- José A. Alonso Jiménez
-- Sevilla, 31 de julio de 2021
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que las sucesiones acotadas por cero son nulas.
-- ------------------------------------------------------------------ *)

theory Las_sucesiones_acotadas_por_cero_son_nulas
imports Main HOL.Real
begin

(* 1\<ordfeminine> demostración *)
lemma
  fixes a :: "nat \<Rightarrow> real"
  assumes "\<forall>n. \<bar>a n\<bar> \<le> 0"
  shows   "\<forall>n. a n = 0"
proof (rule allI)
  fix n
  have "\<bar>a n\<bar> = 0"
  proof (rule antisym)
    show "\<bar>a n\<bar> \<le> 0"
      using assms by (rule allE)
  next
    show " 0 \<le> \<bar>a n\<bar>"
      by (rule abs_ge_zero)
  qed
  then show "a n = 0"
    by (simp only: abs_eq_0_iff)
qed

(* 2\<ordfeminine> demostración *)
lemma
  fixes a :: "nat \<Rightarrow> real"
  assumes "\<forall>n. \<bar>a n\<bar> \<le> 0"
  shows   "\<forall>n. a n = 0"
proof (rule allI)
  fix n
  have "\<bar>a n\<bar> = 0"
  proof (rule antisym)
    show "\<bar>a n\<bar> \<le> 0" try
      using assms by (rule allE)
  next
    show " 0 \<le> \<bar>a n\<bar>" 
      by simp
  qed
  then show "a n = 0"
    by simp
qed

(* 3\<ordfeminine> demostración *)
lemma
  fixes a :: "nat \<Rightarrow> real"
  assumes "\<forall>n. \<bar>a n\<bar> \<le> 0"
  shows   "\<forall>n. a n = 0"
proof (rule allI)
  fix n
  have "\<bar>a n\<bar> = 0" 
    using assms by auto
  then show "a n = 0"
    by simp
qed

(* 4\<ordfeminine> demostración *)
lemma
  fixes a :: "nat \<Rightarrow> real"
  assumes "\<forall>n. \<bar>a n\<bar> \<le> 0"
  shows   "\<forall>n. a n = 0"
using assms by auto

end
