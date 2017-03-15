theory RealNumbersAndSequences
  imports Main Natural Order
begin

chapter "I. Principles of the theory of real numbers"
  
section "1. The system of rational numbers and its gaps"

typedecl rational

datatype sign = pos | neg

axiomatization
      zero :: rational
  and quotient :: "sign \<Rightarrow> natural \<Rightarrow> natural \<Rightarrow> rational"
  where quotient_neq_zero: "zero \<noteq> quotient s a b"
    and quotient_eq: "(quotient s a b = quotient t c d) =
                      (s = t \<or> mul_nat a d = mul_nat b c)"
    and rational_exhaust: "(x = zero \<Longrightarrow> P) \<Longrightarrow> (x = quotient s a b \<Longrightarrow> P) \<Longrightarrow> P"

definition "quotient_simple s a b =
  (let c = gcd_nat a b in quotient s (div_nat a c) (div_nat b c))"

lemma quotient_eq_quotient_simple [simp]: "quotient s a b = quotient_simple s a b"
  by (metis quotient_simple_def rational_exhaust)
    
free_constructors case_rational for zero | quotient_simple s a b
proof -
  show "\<And>P y. (y = zero \<Longrightarrow> P) \<Longrightarrow> (\<And>s a b. y = quotient_simple s a b \<Longrightarrow> P) \<Longrightarrow> P"
    using rational_exhaust quotient_eq_quotient_simple by metis
  show "\<And>a b c x y z. (quotient_simple a b c = quotient_simple x y z) = (a = x \<and> b = y \<and> c = z)"
    apply (simp only: quotient_eq Let_def quotient_simple_def)
    apply standard

    
    
      
    
    
  

value "case quotient True 1 2 of (quotient a b c) \<Rightarrow> a"

-- "Fundamental Laws of Order"
 
theorem 1:
  "a = a"
  "a = b \<Longrightarrow> b = a"
  "a = b \<Longrightarrow> b = c \<Longrightarrow> a = c"
  "(a \<le> b \<and> b < c) \<or> (a < b \<and> b \<le> c) \<Longrightarrow> a < c"
  using order_class.trans by auto

class number = order +
  fixes add :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "+" 65)
  fixes sub :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "-" 65)
  fixes mul :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "*" 70)
  fixes div :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "'/" 70)
  fixes zero :: "'a"
  assumes addition:
    "\<exists> c. a + b = c"
    "a = a' \<Longrightarrow> b = b' \<Longrightarrow> a + b = a' + b'"
    "a + b = b + a"
    "(a + b) + c = a + (b + c)"
    "a < b \<Longrightarrow> a + c < b + c"
  assumes subtraction:
    "\<exists> c. a + c = b"
    "a + c = b \<Longrightarrow> b - a = c"
  assumes multiplication:
    "\<exists> c. a * b = c"
    "a = a' \<Longrightarrow> b = b' \<Longrightarrow> a * b = a' * b'"
    "a * b = b * a"
    "(a * b) * c = a * (b * c)"
    "a < b \<Longrightarrow> c > zero \<Longrightarrow> a * c < b * c"
  assumes division:
    "a \<noteq> zero \<Longrightarrow> \<exists> c. a * c = b"
    "a \<noteq> zero \<Longrightarrow> a * c = b \<Longrightarrow> b / a = c"

instantiation rational :: order
begin

definition lt_rational :: "rational \<Rightarrow> rational \<Rightarrow> bool" where
  "lt_rational a b = (case a of _ \<Rightarrow> _)"