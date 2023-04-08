inductive mynat : Type
| zero : mynat
| succ : mynat -> mynat

namespace mynat

def my_add : mynat -> mynat -> mynat
| zero b := b
| (succ a) b := succ ( my_add a b )

/-for all n: n + 0 = 0-/
lemma add_zero (a : mynat) : my_add a zero = a :=
begin
induction a,
{refl},
{rw my_add,
rw a_ih
}
end

lemma add_succ (a b : mynat) : my_add a (succ b) = succ (my_add a b ):=
begin
induction a,
{
  rw my_add, 
  rw my_add,
},
{rw my_add,
rw my_add,
rw a_ih,}
end 

lemma my_add_comm (a b : mynat) : my_add a b = my_add b a :=
begin
induction a, 
{rw my_add,
rw add_zero},
{rw my_add,
rw a_ih,
rw add_succ}
end

def my_mul : mynat -> mynat -> mynat
| zero b := zero
| (succ a) b := my_add b (my_mul a b)

#reduce my_mul zero.succ.succ zero.succ.succ.succ

lemma mul_zero (a : mynat) : my_mul a zero = zero :=
begin
induction a,
{rw my_mul},
{rw my_mul,
rw a_ih,
rw add_zero}
end

lemma my_mul_comm (a b : mynat) : my_mul a b = my_mul b a :=
begin
induction a,
{rw mul_zero,
rw my_mul},
{rw my_mul,
rw a_ih,
sorry}
end

-- define the <= relation
def less_eq_than: mynat → mynat → Prop
| zero a := true
| (succ a) zero := false
| (succ a) (succ b) := less_eq_than a b
 
-- proofing less_eq_than is decidable
instance less_eq_than_decidable (a b : mynat) : decidable (less_eq_than a b):=
begin
induction a,
{rw less_eq_than, apply_instance, --warum löst apply_instance das Problem???
-- was macht diese Taktik?
},
{
 sorry -- der Induktionschritt kann nicht bewiesen werden da er falsch ist --> anderen Weg suchen
}
end

 #reduce less_eq_than (succ (succ zero)) (succ zero)

-- define division with rest (dividen -> mod -> rest)
def div_rest (x m : mynat) : mynat := 
if (less_eq_than x m) then
  x
else
  x

#eval div_rest zero.succ zero.succ.succ

end mynat