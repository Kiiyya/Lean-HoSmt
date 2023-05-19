inductive All (P : α -> Prop) : List α -> Prop
| nil : All P List.nil
| cons : P x -> All P xs -> All P (List.cons x xs)
