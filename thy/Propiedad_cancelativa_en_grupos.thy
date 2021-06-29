(* Propiedad_cancelativa_en_grupos.thy
-- Propiedad cancelativa en grupos
-- José A. Alonso Jiménez
-- Sevilla, 8 de julio de 2021
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Sea G un grupo y a,b,c \<in> G. Demostrar que si a * b = a* c, entonces
-- b = c.
-- ------------------------------------------------------------------ *)

theory Propiedad_cancelativa_en_grupos
imports Main
begin

context group
begin

(* 1\<ordfeminine> demostración *)

lemma 
  assumes "a \<^bold>* b = a \<^bold>* c"
  shows   "b = c"
proof -
  have "b = \<^bold>1 \<^bold>* b"                     by (simp only: left_neutral)
  also have "\<dots> = (inverse a \<^bold>* a) \<^bold>* b" by (simp only: left_inverse)
  also have "\<dots> = inverse a \<^bold>* (a \<^bold>* b)" by (simp only: assoc)
  also have "\<dots> = inverse a \<^bold>* (a \<^bold>* c)" by (simp only: \<open>a \<^bold>* b = a \<^bold>* c\<close>) 
  also have "\<dots> = (inverse a \<^bold>* a) \<^bold>* c" by (simp only: assoc)
  also have "\<dots> = \<^bold>1 \<^bold>* c"               by (simp only: left_inverse)
  also have "\<dots> = c"                   by (simp only: left_neutral)
  finally show "b = c"                 by this
qed

(* 2\<ordfeminine> demostración *)

lemma 
  assumes "a \<^bold>* b = a \<^bold>* c"
  shows   "b = c"
proof -
  have "b = \<^bold>1 \<^bold>* b"                     by simp
  also have "\<dots> = (inverse a \<^bold>* a) \<^bold>* b" by simp
  also have "\<dots> = inverse a \<^bold>* (a \<^bold>* b)" by (simp only: assoc)
  also have "\<dots> = inverse a \<^bold>* (a \<^bold>* c)" using \<open>a \<^bold>* b = a \<^bold>* c\<close> by simp
  also have "\<dots> = (inverse a \<^bold>* a) \<^bold>* c" by (simp only: assoc)
  also have "\<dots> = \<^bold>1 \<^bold>* c"               by simp
  finally show "b = c"                 by simp
qed

(* 3\<ordfeminine> demostración *)

lemma 
  assumes "a \<^bold>* b = a \<^bold>* c"
  shows   "b = c"
proof -
  have "b = (inverse a \<^bold>* a) \<^bold>* b"       by simp
  also have "\<dots> = inverse a \<^bold>* (a \<^bold>* b)" by (simp only: assoc)
  also have "\<dots> = inverse a \<^bold>* (a \<^bold>* c)" using \<open>a \<^bold>* b = a \<^bold>* c\<close> by simp
  also have "\<dots> = (inverse a \<^bold>* a) \<^bold>* c" by (simp only: assoc)
  finally show "b = c"                 by simp
qed

(* 4\<ordfeminine> demostración *)

lemma 
  assumes "a \<^bold>* b = a \<^bold>* c"
  shows   "b = c"
proof -
  have "inverse a \<^bold>* (a \<^bold>* b) = inverse a \<^bold>* (a \<^bold>* c)"
    by (simp only: \<open>a \<^bold>* b = a \<^bold>* c\<close>)
  then have "(inverse a \<^bold>* a) \<^bold>* b = (inverse a \<^bold>* a) \<^bold>* c"
    by (simp only: assoc)
  then have "\<^bold>1 \<^bold>* b = \<^bold>1 \<^bold>* c"
    by (simp only: left_inverse)
  then show "b = c"
    by (simp only: left_neutral)
qed

(* 5\<ordfeminine> demostración *)

lemma 
  assumes "a \<^bold>* b = a \<^bold>* c"
  shows   "b = c"
proof -
  have "inverse a \<^bold>* (a \<^bold>* b) = inverse a \<^bold>* (a \<^bold>* c)"
    by (simp only: \<open>a \<^bold>* b = a \<^bold>* c\<close>)
  then have "(inverse a \<^bold>* a) \<^bold>* b = (inverse a \<^bold>* a) \<^bold>* c"
    by (simp only: assoc)
  then have "\<^bold>1 \<^bold>* b = \<^bold>1 \<^bold>* c"
    by (simp only: left_inverse)
  then show "b = c"
    by (simp only: left_neutral)
qed

(* 6\<ordfeminine> demostración *)

lemma 
  assumes "a \<^bold>* b = a \<^bold>* c"
  shows   "b = c"
proof -
  have "inverse a \<^bold>* (a \<^bold>* b) = inverse a \<^bold>* (a \<^bold>* c)"
    using \<open>a \<^bold>* b = a \<^bold>* c\<close> by simp
  then have "(inverse a \<^bold>* a) \<^bold>* b = (inverse a \<^bold>* a) \<^bold>* c"
    by (simp only: assoc)
  then have "\<^bold>1 \<^bold>* b = \<^bold>1 \<^bold>* c"
    by simp
  then show "b = c"
    by simp
qed

(* 7\<ordfeminine> demostración *)

lemma 
  assumes "a \<^bold>* b = a \<^bold>* c"
  shows   "b = c"
  using assms
  by (simp only: left_cancel)

end

end

(*
-- Referencias
-- ===========

-- Propiedad 3.22 del libro "Abstract algebra: Theory and applications"
-- de Thomas W. Judson.
-- http://abstract.ups.edu/download/aata-20200730.pdf
*)
