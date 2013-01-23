Class SDenoted (T : Set) : Type :=
{ sdenote : T -> Set
}.
Notation "s[[ x ]]" := (sdenote x).

Definition optsdenote {T} `{SDenoted T} (ox : option T) :=
  match ox with
  | None => False
  | Some x => s[[ x ]]
  end.
Notation "s[! x !]" := (optsdenote x).

Instance SDenoted_option {T} `{ SDenoted T } : SDenoted (option T) :=
{ sdenote := optsdenote
}.

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
