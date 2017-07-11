-module(expr).
-compile([export_all]).

% James Yorston
% JWGY4
% Functional & Concurrent Programming
% Assignment 2
% 13/02/2017


%
% A suite of functions for handling arithmetical expressions
%

% Expressions are represented like this
%
%     {num, N}
%     {var, A}
%     {add, E1, E2}
%     {mul, E1, E2}
%     {abs, E1}
%     {con, E1,E2,E3}
%
% where N is a number, A is an atom,
% and E1, E2 are themselves expressions,

-type expr() :: {'num',integer()}
             |  {'var',atom()}
             |  {'add',expr(),expr()}
             |  {'mul',expr(),expr()}
             |  {'con',expr(),expr(),expr()}.

% For example,
%   {add,{var,a},{mul,{num,2},{var,b}}
% represents the mathematical expression
%   (a+(2*b))

%
% Printing
%

% Turn an expression into a string, so that
%   {add,{var,a},{mul,{num,2},{var,b}}
% is turned into
%   "(a+(2*b))"

-spec print(expr()) -> string().

print({num,N}) ->
    integer_to_list(N);
print({var,A}) ->
    atom_to_list(A);
print({add,E1,E2}) ->
    "("++ print(E1) ++ "+" ++ print(E2) ++")";
print({mul,E1,E2}) ->
    "("++ print(E1) ++ "*" ++ print(E2) ++")";
print({con,E1,E2,E3}) ->
  "<" ++ print(E1) ++ "?" ++ print(E2) ++ ":" ++ print(E3) ++ ">".

%
% parsing
%

% recognise expressions
% deterministic, recursive descent, parser.

% the function returns two things
%   - an expression recognised at the beginning of the string
%     (in fact, the longers such expression)
%   - whatever of the string is left
%
% for example, parse("(-55*eeee)+1111)") is
%   {{mul,{num,-55},{var,eeee}} , "+1111)"}


% recognise a fully-bracketed expression, with no spaces etc.

-spec parse(string()) -> {expr(), string()}.


% Parse a conditional expression
parse([$<|Rest]) ->
    {E1,[$?|Rest1]} = parse(Rest),
    {E2,[$:|Rest2]} = parse(Rest1),
    {E3,[$>|Rest3]} = parse(Rest2),
    {{con,E1,E2,E3},Rest3};

% Normal Expression
parse([$(|Rest]) ->                           % starts with a '('
      {E1,Rest1}     = parse(Rest),           % then an expression
      [Op|Rest2]    = Rest1,                  % then an operator, '+' or '*'
      {E2,Rest3}     = parse(Rest2),          % then another expression
      [$)|RestFinal] = Rest3,                 % starts with a ')'
      {case Op of
	  $+ -> {add,E1,E2};
	  $* -> {mul,E1,E2}
        end,
       RestFinal};

% recognise an integer, a sequence of digits
% with an optional '-' sign at the start

parse([Ch|Rest]) when ($0 =< Ch andalso Ch =< $9) orelse Ch==$- ->
    {Succeeds,Remainder} = get_while(fun is_digit/1,Rest),
    {{num, list_to_integer([Ch|Succeeds])}, Remainder};

% recognise a variable: an atom built of small letters only.

parse([Ch|Rest])  when $a =< Ch andalso Ch =< $z ->
    {Succeeds,Remainder} = get_while(fun is_alpha/1,Rest),
    {{var, list_to_atom([Ch|Succeeds])}, Remainder}.

% auxiliary functions

% recognise a digit

-spec is_digit(integer()) -> boolean().

is_digit(Ch) ->
    $0 =< Ch andalso Ch =< $9.

% recognise a small letter

-spec is_alpha(integer()) -> boolean().

is_alpha(Ch) ->
    $a =< Ch andalso Ch =< $z.

% the longest initial segment of a list in which all
% elements have property P. Used in parsing integers
% and variables

-spec get_while(fun((T) -> boolean()),[T]) -> {[T],[T]}.
%-spec get_while(fun((T) -> boolean()),[T]) -> [T].

get_while(P,[Ch|Rest]) ->
    case P(Ch) of
	true ->
	    {Succeeds,Remainder} = get_while(P,Rest),
	    {[Ch|Succeeds],Remainder};
	false ->
	    {[],[Ch|Rest]}
    end;
get_while(_P,[]) ->
    {[],[]}.

%
% Evaluate an expression
% Extended with conditional expresions
%

% First version commented out.
-type env() :: [{atom(),integer()}].

-spec eval(env(),expr()) -> integer().

eval(_Env,{num,N}) ->
    N;
eval(Env,{var,A}) ->
    lookup(A,Env);
eval(Env,{add,E1,E2}) ->
    eval(Env,E1) + eval(Env,E2);
eval(Env,{mul,E1,E2}) ->
    eval(Env,E1) * eval(Env,E2);
eval(Env,{con,E1,E2,E3}) ->
    case eval(Env,E1) of
      0 -> eval(Env,E2);
      _ -> eval(Env,E3)
    end.

%
% Compiler and virtual machine
%

% Instructions
%    {push, N} - push integer N onto the stack
%    {fetch, A} - lookup value of variable a and push the result onto the stack
%    {add2} - pop the top two elements of the stack, add, and push the result
%    {mul2} - pop the top two elements of the stack, multiply, and push the result

-type instr() :: {'push',integer()}
              |  {'fetch',atom()}
              |  {'add2'}
              |  {'mul2'}
              |  {'con2'}.

-type program() :: [instr()].

% compiler
% Extended by JWGY4 to include abs
% Extended to include conditional expressions

-spec compile(expr()) -> program().

compile({num,N}) ->
    [{push, N}];
compile({var,A}) ->
    [{fetch, A}];
compile({add,E1,E2}) ->
    compile(E1) ++ compile(E2) ++[{add2}];
compile({mul,E1,E2}) ->
    compile(E1) ++ compile(E2) ++[{mul2}];
compile({con,E1,E2,E3}) ->
  compile(E1) ++ compile(E2) ++ compile(E3) ++ [{con2}].


% run a code sequence in given environment and empty stack

-spec run(program(),env()) -> integer().

run(Code,Env) ->
    run(Code,Env,[]).

% execute an instruction, and when the code is exhausted,
% return the top of the stack as result.
% classic tail recursion
% Extended by JWGY4 with abs and con type

-type stack() :: [integer()].

-spec run(program(),env(),stack()) -> integer().

run([{push, N} | Continue], Env, Stack) ->
    run(Continue, Env, [N | Stack]);
run([{fetch, A} | Continue], Env, Stack) ->
    run(Continue, Env, [lookup(A,Env) | Stack]);
run([{add2} | Continue], Env, [N1,N2|Stack]) ->
    run(Continue, Env, [(N1+N2) | Stack]);
run([{mul2} | Continue], Env ,[N1,N2|Stack]) ->
    run(Continue, Env, [(N1*N2) | Stack]);
run([{con2} | Continue], Env ,[N1,N2,N3|Stack]) ->
    case N3 of
      0 -> run(Continue,Env,[N2|Stack]);
      _ -> run(Continue,Env,[N1|Stack])
    end;
run([],_Env,[N]) ->
    N.

% compile and run ...
% should be identical to eval(Env,Expr)

-spec execute(env(),expr()) -> integer().

execute(Env,Expr) ->
    run(compile(Expr),Env).

%
% Simplify an expression
% Extended for conidtional expressions
% Modified for better simplification
%
-spec simplify(expr()) -> expr().

simplify({add,E1,{num,0}}) ->
    simplify(E1);
simplify({add,{num,0},E2}) ->
    simplify(E2);
simplify({mul,E1,{num,1}}) ->
    simplify(E1);
simplify({mul,{num,1},E2}) ->
    simplify(E2);
simplify({mul,_,{num,0}}) ->
    {num,0};
simplify({mul,{num,0},_}) ->
    {num,0};
simplify({add,E1,E2}) ->
    case simplify(E1) of
      {num,0} -> {num,0};
      _       -> {add,simplify(E1),simplify(E2)}
    end;
simplify({mul,E1,E2}) ->
    case simplify(E1) of
      {num,0} -> {num,0};
      _       -> {mul,simplify(E1),simplify(E2)}
    end;
simplify({con,E1,E2,E3}) ->
    case simplify(E1) of
      {num,0} -> simplify(E2);
      _       -> simplify(E3)
    end;
simplify(E) ->
    E.

% Auxiliary function: lookup a
% key in a list of key-value pairs.
% Fails if the key not present.

-spec lookup(atom(),env()) -> integer().

lookup(A,[{A,V}|_]) ->
    V;
lookup(A,[_|Rest]) ->
    lookup(A,Rest).

% Test data.

-spec env1() -> env().
env1() ->
    [{a,23},{b,-12}].

-spec expr1() -> expr().
expr1() ->
    {add,{var,a},{mul,{num,2},{var,b}}}.

-spec test1() -> integer().
test1() ->
    eval(env1(),expr1()).

-spec expr2() -> expr().
expr2() ->
    {add,{mul,{num,1},{var,b}},{mul,{add,{mul,{num,2},{var,b}},{mul,{num,1},{var,b}}},{num,0}}}.

% JWGY4 Test Data
-spec con_run_test() -> integer().
con_run_test() ->
  run(compile({con,{var,a},{var,b},{var,c}}),[{a,1},{b,1},{c,2}]).

-spec con_eval_test() -> integer().
con_eval_test() ->
  eval([],{con,{add,{num,0},{num,0}},{num,1},{num,2}}).

-spec con_print_test() -> integer().
con_print_test() ->
  print({con,{add,{num,0},{num,0}},{num,1},{num,2}}).

-spec con_parse_test() -> expr().
con_parse_test() ->
  parse("<(0+0)?1:2>").

-spec con_simplify_test() -> expr().
con_simplify_test() ->
  simplify({con,{add,{num,0},{num,0}},{mul,{num,1},{num,3}},{num,2}}).

-spec con_simplify_test2() -> expr().
con_simplify_test2() ->
  simplify({mul,{con,{add,{num,0},{num,0}},{mul,{num,1},{num,3}},{num,2}},{num,3}}).

-spec simplify_test() -> expr().
simplify_test() ->
  simplify(expr2()).
