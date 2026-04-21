%token EOF

%start <unit> main

%%

main:
  | EOF { () }
