Class Denoted (T : Type) : Type :=
{ denote : T -> Type
}.
Notation "[[ x ]]" := (denote x).

Definition optdenote {T} `{Denoted T} (ox : option T) :=
  match ox with
  | None => False
  | Some x => [[ x ]]
  end.
Notation "[! x !]" := (optdenote x).

Instance Denoted_option {T} `{ Denoted T } : Denoted (option T) :=
{ denote := optdenote
}.
