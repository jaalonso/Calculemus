import algebra.group.basic

example
  {M : Type} [monoid M]
  (h : ∀ x : M, x * x = 1)
  : ∀ x y : M, x * y = y * x :=
begin
  intros a b,
  calc a * b
       = (a * b) * 1
         : (mul_one (a * b)).symm
   ... = (a * b) * (a * a)
         : congr_arg ((*) (a*b)) (h a).symm
   ... = ((a * b) * a) * a
         : (mul_assoc (a*b) a a).symm
   ... = (a * (b * a)) * a
         : congr_arg (* a) (mul_assoc a b a)
   ... = (1 * (a * (b * a))) * a
         : congr_arg (* a) (one_mul (a*(b*a))).symm
   ... = ((b * b) * (a * (b * a))) * a
         : congr_arg (* a) (congr_arg (* (a*(b*a))) (h b).symm)
   ... = (b * (b * (a * (b * a)))) * a
         : congr_arg (* a) (mul_assoc b b (a*(b*a)))
   ... = (b * ((b * a) * (b * a))) * a
         : congr_arg (* a) (congr_arg ((*) b) (mul_assoc b a (b*a)).symm)
   ... = (b * 1) * a
         : congr_arg (* a) (congr_arg ((*) b) (h (b*a)))
   ... = b * a
         : congr_arg (* a) (mul_one b),
end
