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

def my_mul (a b: mynat) : mynat -> mynat -> mynat
| zero b := zero
| (succ a) b := my_add a (my_mul a b)


end mynat
