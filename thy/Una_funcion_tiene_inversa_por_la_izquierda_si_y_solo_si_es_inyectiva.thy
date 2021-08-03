(* Una_funcion_tiene_inversa_por_la_izquierda_si_y_solo_si_es_inyectiva.thy
-- Una función tiene inversa por la izquierda si y solo si es inyectiva
-- José A. Alonso Jiménez
-- Sevilla, 4 de agosto de 2021
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- En Isabelle/HOL, se puede definir que f tenga inversa por la
-- izquierda por
--    definition tiene_inversa_izq :: "('a \<Rightarrow> 'b) \<Rightarrow> bool" where
--      "tiene_inversa_izq f \<longleftrightarrow> (\<exists>g. \<forall>x. g (f x) = x)"
-- Además, que f es inyectiva sobre un conjunto está definido por
--    definition inj_on :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> bool"
--      where "inj_on f A \<longleftrightarrow> (\<forall>x\<in>A. \<forall>y\<in>A. f x = f y \<longrightarrow> x = y)"
-- y que f es inyectiva por
--    abbreviation inj :: "('a \<Rightarrow> 'b) \<Rightarrow> bool"
--       where "inj f \<equiv> inj_on f UNIV"
--
-- Demostrar que una función f, con dominio no vacío, tiene inversa por
-- la izquierda si y solo si es inyectiva.
-- ------------------------------------------------------------------ *)

theory Una_funcion_tiene_inversa_por_la_izquierda_si_y_solo_si_es_inyectiva
imports Main
begin

definition tiene_inversa_izq :: "('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "tiene_inversa_izq f \<longleftrightarrow> (\<exists>g. \<forall>x. g (f x) = x)"

(* 1\<ordfeminine> demostración *)
lemma
  "tiene_inversa_izq f \<longleftrightarrow> inj f"
proof (rule iffI)
  assume "tiene_inversa_izq f"
  show "inj f"
  proof (unfold inj_def; intro allI impI)
    fix x y
    assume "f x = f y"
    obtain g where hg : "\<forall>x. g (f x) = x"
      using \<open>tiene_inversa_izq f\<close> tiene_inversa_izq_def
      by auto
    have "x = g (f x)"
      by (simp only: hg)
    also have "\<dots> = g (f y)"
      by (simp only: \<open>f x = f y\<close>)
    also have "\<dots> = y"
      by (simp only: hg)
    finally show "x = y" .
  qed
next
  assume "inj f"
  show "tiene_inversa_izq f"
  proof (unfold tiene_inversa_izq_def)
    have "\<forall>x. inv f (f x) = x"
    proof (rule allI)
      fix x
      show "inv f (f x) = x"
        using \<open>inj f\<close> by (simp only: inv_f_f)
    qed
  then show "(\<exists>g. \<forall>x. g (f x) = x)"
    by (simp only: exI)
  qed
qed

(* 2\<ordfeminine> demostración *)
lemma
  "tiene_inversa_izq f \<longleftrightarrow> inj f"
proof (rule iffI)
  assume "tiene_inversa_izq f"
  then show "inj f"
    by (metis inj_def tiene_inversa_izq_def)
next
  assume "inj f"
  then show "tiene_inversa_izq f"
    by (metis the_inv_f_f tiene_inversa_izq_def)
qed

(* 3\<ordfeminine> demostración *)
lemma
  "tiene_inversa_izq f \<longleftrightarrow> inj f"
by (metis tiene_inversa_izq_def inj_def the_inv_f_f)

end
