(* Unicidad_de_los_inversos_en_los_grupos.thy
-- Unicidad de los inversos en los grupos
-- José A. Alonso Jiménez
-- Sevilla, 5 de julio de 2021
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que si a es un elemento de un grupo G, entonces a tiene un
-- único inverso; es decir, si b es un elemento de G tal que a * b = 1,
-- entonces b es inverso de a.
-- ------------------------------------------------------------------ *)

theory Unicidad_de_los_inversos_en_los_grupos
imports Main
begin

context group
begin

thm left_inverse right_cancel

(* ?\<ordfeminine> demostración *)

lemma
  assumes "a \<^bold>* b = \<^bold>1"
  shows "inverse a = b"
proof -
  have "inverse a = inverse a \<^bold>* \<^bold>1"     by (simp only: right_neutral)
  also have "\<dots> = inverse a \<^bold>* (a \<^bold>* b)" by (simp only: assms(1))
  also have "\<dots> = (inverse a \<^bold>* a) \<^bold>* b" by (simp only: assoc [symmetric])
  also have "\<dots> = \<^bold>1 \<^bold>* b"               by (simp only: left_inverse)
  also have "\<dots> = b"                   by (simp only: left_neutral)
  finally show "inverse a = b"         by this
qed

(* ?\<ordfeminine> demostración *)

lemma
  assumes "a \<^bold>* b = \<^bold>1"
  shows "inverse a = b"
proof -
  have "inverse a = inverse a \<^bold>* \<^bold>1"     by simp
  also have "\<dots> = inverse a \<^bold>* (a \<^bold>* b)" using assms by simp
  also have "\<dots> = (inverse a \<^bold>* a) \<^bold>* b" by (simp add: assoc [symmetric])
  also have "\<dots> = \<^bold>1 \<^bold>* b"               by simp
  also have "\<dots> = b"                   by simp
  finally show "inverse a = b"         .
qed

(* ?\<ordfeminine> demostración *)

lemma
  assumes "a \<^bold>* b = \<^bold>1"
  shows "inverse a = b"
proof -
  from assms have "inverse a \<^bold>* (a \<^bold>* b) = inverse a"
    by simp
  then show "inverse a = b"
    by (simp add: assoc [symmetric])
qed

(* ?\<ordfeminine> demostración *)

lemma
  assumes "a \<^bold>* b = \<^bold>1"
  shows "inverse a = b"
  using assms
  by (simp only: inverse_unique)

end

end


(*
-- Referencia
-- ==========

-- Propiedad 3.18 del libro "Abstract algebra: Theory and applications"
-- de Thomas W. Judson.
-- http://abstract.ups.edu/download/aata-20200730.pdf#page=49
*)
