-- Un_numero_es_par_syss_lo_es_su_cuadrado.lean
-- Un número es par si y solo si lo es su cuadrado
-- José A. Alonso Jiménez
-- Sevilla, 24 de julio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que un número es par si y solo si lo es su cuadrado.
-- ---------------------------------------------------------------------

import data.int.parity
import tactic
open int

variable (n : ℤ)

-- 1ª demostración
example :
  even (n^2) ↔ even n :=
begin
  split,
  { contrapose,
    rw ← odd_iff_not_even,
    rw ← odd_iff_not_even,
    unfold odd,
    intro h,
    cases h with k hk,
    use 2*k*(k+1),
    rw hk,
    ring, },
  { unfold even,
    intro h,
    cases h with k hk,
    use 2*k^2,
    rw hk,
    ring, },
end

-- 2ª demostración
example :
  even (n^2) ↔ even n :=
begin
  split,
  { contrapose,
    rw ← odd_iff_not_even,
    rw ← odd_iff_not_even,
    rintro ⟨k, rfl⟩,
    use 2*k*(k+1),
    ring, },
  { rintro ⟨k, rfl⟩,
    use 2*k^2,
    ring, },
end

-- 3ª demostración
example :
  even (n^2) ↔ even n :=
iff.intro
  ( have h : ¬even n → ¬even (n^2),
      { assume h1 : ¬even n,
        have h2 : odd n,
          from odd_iff_not_even.mpr h1,
        have h3: odd (n^2), from
          exists.elim h2
            ( assume k,
              assume hk : n = 2*k+1,
              have h4 : n^2 = 2*(2*k*(k+1))+1, from
                calc  n^2
                    = (2*k+1)^2       : by rw hk
                ... = 4*k^2+4*k+1     : by ring
                ... = 2*(2*k*(k+1))+1 : by ring,
              show odd (n^2),
                from exists.intro (2*k*(k+1)) h4),
        show ¬even (n^2),
          from odd_iff_not_even.mp h3 },
    show even (n^2) → even n,
      from not_imp_not.mp h )
  ( assume h1 : even n,
    show even (n^2), from
      exists.elim h1
        ( assume k,
          assume hk : n = k + k ,
          have h2 : n^2 = 2*k^2 + 2*k^2, from
            calc  n^2
                = (k + k)^2  : by rw hk
            ... = 2*k^2 + 2*k^2 : by ring,
          show even (n^2),
            from exists.intro (2*k^2) h2 ))

-- 4ª demostración
example :
  even (n^2) ↔ even n :=
calc even (n^2)
     ↔ even (n * n)      : iff_of_eq (congr_arg even (sq n))
 ... ↔ (even n ∨ even n) : int.even_mul
 ... ↔ even n            : or_self (even n)

-- 5ª demostración
example :
  even (n^2) ↔ even n :=
calc even (n^2)
     ↔ even (n * n)      : by ring_nf
 ... ↔ (even n ∨ even n) : int.even_mul
 ... ↔ even n            : by simp

-- 6ª demostración
example :
  even (n^2) ↔ even n :=
begin
  split,
  { contrapose,
    intro h,
    rw ← odd_iff_not_even at *,
    cases h with k hk,
    use 2*k*(k+1),
    calc n^2
         = (2*k+1)^2       : by rw hk
     ... = 4*k^2+4*k+1     : by ring
     ... = 2*(2*k*(k+1))+1 : by ring, },
  { intro h,
    cases h with k hk,
    use 2*k^2,
    calc n^2
         = (k + k)^2     : by rw hk
     ... = 2*k^2 + 2*k^2 : by ring, },
end
