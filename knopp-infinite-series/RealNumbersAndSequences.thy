theory RealNumbersAndSequences
  imports Main Natural Order
begin

chapter "I. Principles of the theory of real numbers"
  
section "1. The system of rational numbers and its gaps"


value "a < b"

instantiation natural :: order
begin

instance proof
  fix a b c :: natural
  show "(a < b) = (a \<noteq> b \<and> \<not> b < a)"
       "(a = b) = (\<not> a < b \<and> \<not> b < a)"
       "(b < a) = (\<not> a < b \<and> a \<noteq> b)"
    using lt_natural.elims(3) by (induction a b rule: lt_natural.induct, auto)+
  show "\<not> b < a \<Longrightarrow> b < c \<Longrightarrow> a < c"
       "a < b \<Longrightarrow> \<not> c < b \<Longrightarrow> a < c"
    by (induction a c arbitrary: b rule: lt_natural.induct; auto;
        metis natural.distinct(1) natural.inject lt_natural.elims(2) lt_natural.elims(3))+
qed

end

    
definition (in order) min :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "min a b = (if a < b then a else b)"

definition (in order) max :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "max a b = (if a > b then a else b)"

    

typedecl rational

axiomatization zero_rational :: rational
  and quotient :: "bool \<Rightarrow> natural \<Rightarrow> natural \<Rightarrow> rational"
  where quotient_neq_zero: "zero_rational \<noteq> quotient s a b"
    and quotient_eq: "s = t \<Longrightarrow> mul_nat a d = mul_nat b c \<Longrightarrow>
                      quotient s a b = quotient t c d"

-- "Fundamental Laws of Order"
 
theorem 1:
  "a = a"
  "a = b \<Longrightarrow> b = a"
  "a = b \<Longrightarrow> b = c \<Longrightarrow> a = c"
  "(a \<le> b \<and> b < c) \<or> (a < b \<and> b \<le> c) \<Longrightarrow> a < c"
  using order_class.trans by (auto, fastforce+)

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
  "lt_rational a b = "