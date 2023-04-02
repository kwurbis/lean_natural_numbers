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
sorry
end 

end mynat
