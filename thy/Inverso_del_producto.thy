(* Inverso_del_producto.thy
-- Inverso del producto
-- José A. Alonso Jiménez
-- Sevilla, 6 de julio de 2021
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Sea G un grupo y a, b \<in> G. Entonces,
--    (a * b)⁻¹ = b⁻¹ * a⁻¹
-- ------------------------------------------------------------------ *)

theory Inverso_del_producto
imports Main
begin

context group
begin

(* 1\<ordfeminine> demostración *)

lemma "inverse (a \<^bold>* b) = inverse b \<^bold>* inverse a"
proof (rule inverse_unique)
  have "(a \<^bold>* b) \<^bold>* (inverse b \<^bold>* inverse a) =
        ((a \<^bold>* b) \<^bold>* inverse b) \<^bold>* inverse a"
    by (simp only: assoc)
  also have "\<dots> = (a \<^bold>* (b \<^bold>* inverse b)) \<^bold>* inverse a"
    by (simp only: assoc)
  also have "\<dots> = (a \<^bold>* \<^bold>1) \<^bold>* inverse a"
    by (simp only: right_inverse)
  also have "\<dots> = a \<^bold>* inverse a"
    by (simp only: right_neutral)
  also have "\<dots> = \<^bold>1"
    by (simp only: right_inverse)
  finally show "a \<^bold>* b \<^bold>* (inverse b \<^bold>* inverse a) = \<^bold>1"
    by this
qed

(* 2\<ordfeminine> demostración *)

lemma "inverse (a \<^bold>* b) = inverse b \<^bold>* inverse a"
proof (rule inverse_unique)
  have "(a \<^bold>* b) \<^bold>* (inverse b \<^bold>* inverse a) =
        ((a \<^bold>* b) \<^bold>* inverse b) \<^bold>* inverse a"
    by (simp only: assoc)
  also have "\<dots> = (a \<^bold>* (b \<^bold>* inverse b)) \<^bold>* inverse a"
    by (simp only: assoc)
  also have "\<dots> = (a \<^bold>* \<^bold>1) \<^bold>* inverse a"
    by simp
  also have "\<dots> = a \<^bold>* inverse a"
    by simp
  also have "\<dots> = \<^bold>1"
    by simp
  finally show "a \<^bold>* b \<^bold>* (inverse b \<^bold>* inverse a) = \<^bold>1"
    .
qed

(* 3\<ordfeminine> demostración *)

lemma "inverse (a \<^bold>* b) = inverse b \<^bold>* inverse a"
proof (rule inverse_unique)
  have "a \<^bold>* b \<^bold>* (inverse b \<^bold>* inverse a) =
        a \<^bold>* (b \<^bold>* inverse b) \<^bold>* inverse a"
    by (simp only: assoc)
  also have "\<dots> = \<^bold>1"
    by simp
  finally show "a \<^bold>* b \<^bold>* (inverse b \<^bold>* inverse a) = \<^bold>1" .
qed

(* 4\<ordfeminine> demostración *)

lemma "inverse (a \<^bold>* b) = inverse b \<^bold>* inverse a"
  by (simp only: inverse_distrib_swap)

(* ?\<ordfeminine> demostración *)

end

end

(*
-- Referencia
-- ==========

-- Propiedad 3.19 del libro "Abstract algebra: Theory and applications"
-- de Thomas W. Judson.
-- http://abstract.ups.edu/download/aata-20200730.pdf#page=49
*)
