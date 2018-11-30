type skillSet =
  Sk1 | Sk2 | Sk3 | Sk4 | Sk5 | Sk6

let skillName = function
  | Sk1 -> ('s' :: ('k' :: ('i' :: ('l' :: ('l' :: ('_' :: ('1' :: [])))))))
  | Sk2 -> ('s' :: ('k' :: ('i' :: ('l' :: ('l' :: ('_' :: ('2' :: [])))))))
  | Sk3 -> ('s' :: ('k' :: ('i' :: ('l' :: ('l' :: ('_' :: ('3' :: [])))))))
  | Sk4 -> ('s' :: ('k' :: ('i' :: ('l' :: ('l' :: ('_' :: ('4' :: [])))))))
  | Sk5 -> ('s' :: ('k' :: ('i' :: ('l' :: ('l' :: ('_' :: ('5' :: [])))))))
  | Sk6 -> ('s' :: ('k' :: ('i' :: ('l' :: ('l' :: ('_' :: ('6' :: [])))))))

let skill_id s =
  match s with
  | "skill_1" -> Sk1
  | "skill_2" -> Sk2
  | "skill_3" -> Sk3
  | "skill_4" -> Sk4
  | "skill_5" -> Sk5
  | "skill_6" -> Sk6
  | _ -> invalid_arg ("unknown skill: " ^ s)
