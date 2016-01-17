
grammar Python;


program : module
        ;

module : (statement|NEWL)*
       ;

statement : simple_statement     # Statement_1
          | compound_statement   # Statement_2
          ;

simple_statement : small_statement_list ';'? NEWL+
                 ;

small_statement_list : small_statement ( ';' small_statement )*
                     ;

small_statement : expression             # Small_statement_1
                | target '=' expression  # Small_statement_2
                | PRINT expression       # Small_statement_3
                | RETURN expression      # Small_statement_4
                ;

opt_semicolon :
              | ';'
              ;

opt_comma :
          | ','
          ;

compound_statement : if_stmt     # Compound_statement_1
                   | while_stmt  # Compound_statement_2
                   | funcdef     # Compound_statement_3
                   | classdef    # Compound_statement_4
                   ;

if_stmt : IF expression ':' suite (ELSE ':' suite)?   # IfInstr
        ;

while_stmt : WHILE expression ':' suite
           ;

funcdef : DEF ID '(' id_list ')' ':' suite
        ;

classdef : CLASS ID ('(' expr_list ','? ')')? ':' suite
         ;

suite : lpar statement_list rpar
      ;

statement_list : statement+        
               ;

target : ID                                           # Target_1
       | subscription                                 # Target_2
       | expression '.' ID                            # Target_3
       ;

expression : TRUE                                             # Expression_1
           | FALSE                                            # Expression_2
           | STRING                                           # Expression_3
           | ID                                               # Expression_4
           | FLOAT                                            # Expression_5
           | INT                                              # Expression_6
           | INPUT '(' ')'                                    # Expression_7
           | expression '(' expr_list ')'                     # Expression_8
           | '(' expression ')'                               # Expression_9
           | '[' expr_list_comma ']'                          # Expression_10
           | '{' key_datum_list '}'                           # Expression_11
           | expression '[' expression ']'                    # Expression_12
           | expression '.' ID                                # Expression_13
           | op=('+'|'-') expression                          # Expression_14
           | expression op=('*'|'/'|'%') expression           # Expression_15
           | expression op=('+'|'-') expression               # Expression_16
           | expression op=(IS|EQ|NEQ|LT|GT|LE|GE) expression # Expression_17
           | NOT expression                                   # Expression_18
           | expression op=AND expression                     # Expression_19
           | expression op=OR expression                      # Expression_20
           | expression IF expression ELSE expression         # Expression_21
           | LAMBDA id_list ':' expression                    # Expression_22
           ;


expr_list_comma : expr_list opt_comma
                ;

expr_list : /* empty */
          | expression (',' expression )*
          ;

key_datum_list 
          : /* empty */
          | key_datum ( ',' key_datum )*
          ;

key_datum : expression ':' expression
          ;

subscription : expression '[' expression ']'
             ;

id_list : /* empty */
        | ID ( ',' ID )*
        ;

lpar : NEWL+ '{' NEWL*
     ;

rpar : NEWL* '}' NEWL+
     ;

AND: 'and' ;
CLASS: 'class' ;
DEF: 'def' ;
ELSE: 'else' ;
FALSE: 'False' ;
IF: 'if' ;
IS: 'is' ;
INPUT: 'input' ;
LAMBDA: 'lambda' ;
NOT: 'not' ;
OR: 'or' ;
PRINT: 'print' ;
RETURN: 'return' ;
TRUE: 'True' ;
WHILE: 'while' ;

ID: (LETTER) (LETTER|DIGIT)* ;
WS: (' '|'\t')+ -> skip ;
NEWL: ('\r'?'\n')|'\r' ;
COMMENT: '/*' .*? '*/' -> skip ;
SL_COMMENT: '#' ~[\r\n]* -> skip ;
INT: DIGIT+ ;
FLOAT: ( DIGIT+ '.' DIGIT* | ('.' DIGIT+) ) EXP? ;
fragment DIGIT: '0'..'9' ;
fragment LETTER: 'a'..'z' | 'A'..'Z' | '_' ;
fragment EXP:  ('e'|'E')('+'|'-')?  DIGIT+ ;

STRING:  '\"' ~('\n'|'\"')* '\"' ;

EQ: '==' ;
NEQ: '!=' ;
LT: '<' ;
GT: '>' ;
LE: '<=' ;
GE: '>=' ;

