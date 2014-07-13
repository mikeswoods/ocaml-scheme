(** 
 * Scheme Interpreter 
 * Author: Mike Woods
 *)
type scheme_val =
	ScmNil |
	ScmBoolean of bool |
	ScmNumber of float |
	ScmString of string |
	ScmSymbol of string |
	ScmPair of scheme_val * scheme_val |
	ScmList of scheme_val list |
	ScmProc of string * ((scheme_val list) -> scheme_env -> scheme_val)
and scheme_env_binding = { name: string ; value: scheme_val } 
and scheme_env = 
	EmptyEnv |
	Env of scheme_env_binding list * scheme_env

exception NoMoreTokens
exception UnbalancedParen
exception ExitToplevel
exception SchemeError of string

let error msg = raise (SchemeError(msg))

let is_whitespace_char = function ' ' | '\t' | '\n' | '\r' -> true | _ -> false 

let is_whitespace_string token_str =
	if token_str == "" then true
	else let n = String.length token_str in
		let rec iter at count =
			if at >= n then count
			else let ch = token_str.[at] in
				iter (succ at) (count + (if (is_whitespace_char ch) then 1 else 0)) in
		(iter n 0) == n

let rec trim_string s =
	let l = String.length s in 
		if l = 0 then s
		else if (is_whitespace_char s.[0]) then trim_string (String.sub s 1 (pred 1))
		else if (is_whitespace_char s.[pred 1]) then trim_string (String.sub s 0 (pred 1))	
		else s

let rec scmval_to_string =
	let rec conslist_to_string = 
		function
			[] -> "" |
			x :: [] -> (scmval_to_string x) |
			x :: xs -> (scmval_to_string x) ^ " " ^ (conslist_to_string xs) in
	let is_integer_val fval = (abs_float (fval -. (floor fval))) < 1.0e-8 in 
	function
		ScmNil -> "Nil" |
		ScmBoolean(true) -> "#t" | ScmBoolean(false) -> "#f" |
		ScmNumber(n) -> if (is_integer_val n) then (string_of_int (truncate n)) else (string_of_float n) |
		ScmString(s) -> s |
		ScmSymbol(s) -> s |
		ScmPair(a,b) -> "(" ^ (scmval_to_string a) ^ " . " ^ (scmval_to_string b) ^ ")" |
		ScmList(l) -> "(" ^ (conslist_to_string l) ^ ")" |
		ScmProc(id, _) -> "Lambda<" ^ id ^ ">"

let scmvals_to_string vals = List.fold_left (fun a b -> a ^ " " ^ b ) "" (List.map scmval_to_string vals)

let scmtype_to_string =
	function
		ScmNil         -> "Nil" |
		ScmBoolean(_)  -> "Boolean" |
		ScmNumber(_)   -> "Number" |
		ScmString(s)   -> "String" |
		ScmSymbol(s)   -> "Symbol" |
		ScmPair(a,b)   -> "Pair" |
	 	ScmList(l)     -> "List" |
		ScmProc(id, _) -> "Procedure"

let print_exp exp = print_endline (scmval_to_string exp)

(* Parsing & tokenizing *)

let tokenize string_of_tokens = 
	let tokens      = ref [] in                                                                                                    
	let char_buffer = ref (Buffer.create 1024) in
	let in_string   = ref false in
	let string_of_char ch = String.make 1 ch in
	let append_char_to_buffer ch = Buffer.add_char !char_buffer ch in
	let flush_and_clear_buffer () = 
		let contents = Buffer.contents !char_buffer in Buffer.clear !char_buffer ; contents	in
	let append_token token = tokens := !tokens @ [token] ; () in
	let strip_whitespace_tokens list_of_tokens =
		List.filter (fun token_string -> not (is_whitespace_string token_string)) list_of_tokens in
	let tokenizer =
		function
			'\"' as delim -> in_string := not !in_string ; append_char_to_buffer delim ; () |
			' ' | '\t' | '\n' as ws -> 
				if !in_string then append_char_to_buffer ws
				else append_token (flush_and_clear_buffer ()) |  
			'\'' | '`' | '(' | ')' as paren -> 
				if !in_string then append_char_to_buffer paren
				else begin append_token (flush_and_clear_buffer ()) ; append_token (string_of_char paren) end |
			ch -> append_char_to_buffer ch in
 	String.iter tokenizer string_of_tokens ;
	append_token (flush_and_clear_buffer ()) ;
	let final_tokens = strip_whitespace_tokens !tokens in
	List.iter (fun s -> Printf.printf "> token = `%s'\n" s ; () ) final_tokens ;
	final_tokens

let rec parse list_of_tokens = 
	let is_quoted_string token_string = 
		(token_string.[0] = '\"') && (token_string.[((String.length token_string) - 1)] = '\"') in
	let unquote_string = function "" | "\"" | "\"\"" -> "" | s -> String.sub s 1 ((String.length s) - 2) in
	let wrap_quote_exp exp = ScmList([ScmSymbol("quote") ; exp ]) in
	let classify token_str =
		let lower_token_str = String.lowercase token_str in
		if (is_quoted_string token_str) then ScmString((unquote_string token_str))
		else if lower_token_str = "#t" then ScmBoolean(true)
		else if lower_token_str = "#f" then ScmBoolean(false)
		else try ScmNumber((float_of_string token_str)) with _ -> ScmSymbol(token_str) in
	let tokens_left = ref list_of_tokens in
	let read_token () = 
		match !tokens_left with
			t :: ts -> tokens_left := ts ; t |
			[] -> raise NoMoreTokens in
	let discard_token () =
		match !tokens_left with
			t :: ts -> tokens_left := ts ; () |
			[] -> raise NoMoreTokens in
	let peek_token () = 
		match !tokens_left with
			t :: ts -> t |
			[] -> raise NoMoreTokens in	
	let rec read_sexp depth = 
		let next_token = peek_token () in
		let use_token = trim_string next_token in
		match use_token with 
			"'" -> discard_token () ; [ wrap_quote_exp (List.hd (read_sexp 0)) ] |
			"(" -> discard_token () ; [ (read_list_item (succ depth) []) ] |
			_ -> [ (read_atom ()) ]
	and read_list_item depth accum =
		match (peek_token ()) with
			")" -> if (depth > 0) then begin discard_token () ; ScmList(accum) end else raise UnbalancedParen |
			_ -> read_list_item (succ depth) (accum @ (read_sexp (succ depth))) 
	and read_atom () = 
		classify (read_token ()) in
	let read' list_of_tokens accum depth =
		let next_token = peek_token () in
			match next_token with
				"'" -> wrap_quote_exp (List.hd (read_sexp 0)) |
				"(" -> List.hd (read_sexp 0) |
				_ -> read_atom () in
	let parsed = read' !tokens_left [] 0 in
	 print_endline ("=> " ^ scmval_to_string parsed) ; 
	parsed

(* sexp manipulation functions *)

let exp_count = function ScmList(lst) -> List.length lst | ScmPair(_, _) -> 2 | e -> 1

let exp_nth cl n = 
	match cl with
		ScmList([]) -> error "nth: Empty list" |
		ScmList(xs) -> List.nth xs n |
		e -> error ("exp_last: Not a List " ^ (scmval_to_string e))

let exp_1st =
	function
		ScmList(_) as cl -> (exp_nth cl 0) |
		ScmPair(a, _) -> a |
		e -> error ("1st: Not a List or Pair: " ^ (scmval_to_string e))

let exp_2nd =
	function
		ScmList(_) as cl -> (exp_nth cl 1) |
		ScmPair(_, b) -> b |
		e -> error ("2nd: Not a List or Pair: " ^ (scmval_to_string e))

let exp_last = 
	function
		ScmList([]) -> error "Empty list" |
		ScmList(xs) -> List.nth xs ((List.length xs) - 1) |
		ScmPair(_, b) -> b |
		e -> error ("last: Not a List or Pair: " ^ (scmval_to_string e))

let exp_rest =
	function
		ScmList([]) -> error "rest: Empty list" |
		ScmList(_ :: xs) -> ScmList(xs) |
		ScmPair(_, b) -> b |
		e -> error ("rest: Not a List or Pair: " ^ (scmval_to_string e))

(* Conversion *)

let as_Singleton = function [a] -> a | _ -> error ("destructure: Not a single exp")
let as_Pair = function [a;b] -> (a,b) | _ -> error ("destructure: Not a pair of exp")

let rec as_CondValue = 
	function 
		ScmNil | ScmBoolean(false) | ScmNumber(0.0) | ScmString("") | ScmSymbol("") -> false |
		ScmPair(a,b) when ((as_CondValue a) = false) or (as_CondValue b) = false -> false |
		ScmList([]) -> false |
		_ -> true

let as_SchmTextType =
	function
		ScmString(s) -> s | ScmSymbol(s) -> s |
		x -> error ("destructure: Not a Symbol or String: " ^ (scmval_to_string x))
let as_SchmTextTypes vals = List.map as_SchmTextType vals

let as_ScmNumber = function ScmNumber(n) -> n | x -> error ("destructure: Not a Number: " ^ (scmval_to_string x))
let as_ScmNumbers vals = List.map as_ScmNumber vals
let as_ScmAggregateType = function ScmList(lst) -> lst | x -> error ("destructure: Not a List: " ^ (scmval_to_string x))

(* Environment functions *)

let env_print env =
	let rec env_print' =
		function
			EmptyEnv -> " -- " |
			Env (bindings, outer_env) ->
				"(" ^
				(List.fold_left
					(fun a b -> a ^ "\n" ^ b)
					""
					(List.map (fun i -> " (\"" ^ i.name ^ "\" " ^ (scmval_to_string i.value) ^ ")") bindings)) ^
				"\n) => \n" ^
				(env_print' outer_env) in
	print_endline (env_print' env)

(* Env exists *)

let rec env_exists env k =
	match env with 
		EmptyEnv -> false |
		Env (bindings, outer_env) ->
			if (List.exists (function { name = k' } when k = k' -> true | _ -> false) bindings) then true else env_exists outer_env k

let env_put env k v = 
	match env with
		EmptyEnv -> Env ( [ { name = k ; value = v } ], EmptyEnv) |
		Env (bindings, enclosing_env) ->
			Env ( { name = k ; value = v } :: (List.filter (function { name = k' } when k = k' -> false | _ -> true) bindings), enclosing_env)

let env_put_many env ks vs = List.fold_left2 (fun env k v -> env_put env k v) env ks vs

(* (scheme_env -> string) -> (scheme_val, bool) *)

let rec env_get env k =
	match env with 
		EmptyEnv -> (ScmNil, false) |
		Env (bindings, outer_env) ->
            let finder = function { name = k' } when k = k' -> true | _ -> false in
                if (List.exists finder bindings) then let b = (List.find finder bindings) in (b.value, true) else env_get outer_env k

let env_init () = 
	let syms = [
		("nil", ScmNil) ;
		("*pi*", ScmNumber(3.1415926535897931)) ;
		("*e*", ScmNumber(2.7182818284590451))
	] in
	let funcs = [
		("quit",      fun args env -> raise ExitToplevel) ;
		("exit",      fun args env -> raise ExitToplevel) ;
		("show-all-symbols", fun args env -> (env_print env) ; ScmNil) ;
		("type?",     fun args env -> ScmList((List.map (fun s -> ScmString(s)) (List.map scmtype_to_string args)))) ;
		(* ("defined?", fun args -> ScmBoolean(((match (as_Singleton args) with ScmSymb(key) -> ))) ; *)
		("nil?",     fun args env ->  ScmBoolean((match (as_Singleton args) with ScmNil -> true | _ -> false))) ;
		("null?",    fun args env ->  
			match (as_Singleton args) with
				ScmList(xs) -> ScmBoolean(((List.length xs) = 0)) |
				x -> error ("Not a list type: " ^ (scmval_to_string x))) ;
		("number?",  fun args env ->  ScmBoolean((match (as_Singleton args) with ScmNumber(_) -> true | _ -> false))) ;
		("string?",  fun args env ->  ScmBoolean((match (as_Singleton args) with ScmString(_) -> true | _ -> false))) ;
		("symbol?",  fun args env ->  ScmBoolean((match (as_Singleton args) with ScmSymbol(_) -> true | _ -> false))) ;
		("list?",    fun args env ->  ScmBoolean((match (as_Singleton args) with ScmList(_) -> true | _ -> false))) ;
		("pair?",    fun args env ->  ScmBoolean((match (as_Singleton args) with ScmPair(_, _) -> true | _ -> false))) ;
		("print",    fun args env -> (List.iter print_exp args) ; ScmNil) ;
		("len",  fun args env -> 
			match (as_Singleton args) with
		 		ScmString(x)  -> ScmNumber((float_of_int (String.length x))) |
				ScmPair(_, _) -> ScmNumber(2.0) |
				ScmList(xs)   -> ScmNumber((float_of_int (List.length xs))) |
				x -> error ("Length not applicable to scalar type: " ^ (scmval_to_string x))) ;
		("=",     fun args env -> ScmBoolean((let (a,b) = as_Pair args in a = b))) ;
		("!=",    fun args env -> ScmBoolean((let (a,b) = as_Pair args in a <> b))) ;
		("<",     fun args env -> ScmBoolean((let (a,b) = as_Pair args in a < b))) ;
		("<=",    fun args env -> ScmBoolean((let (a,b) = as_Pair args in a <= b))) ;
		(">",     fun args env -> ScmBoolean((let (a,b) = as_Pair args in a > b))) ;
		(">=",    fun args env -> ScmBoolean((let (a,b) = as_Pair args in a >= b))) ;
        ("+",     fun args env -> ScmNumber(List.fold_left  ( +. ) 0.0 (List.map as_ScmNumber args))) ;
        ("-",     fun args env -> ScmNumber(List.fold_right ( -. ) (List.map as_ScmNumber args) 0.0)) ;
        ("*",     fun args env -> ScmNumber(List.fold_left  ( *. ) 1.0 (List.map as_ScmNumber args))) ;
        ("/",     fun args env -> ScmNumber(List.fold_right ( /. ) (List.map as_ScmNumber args) 1.0)) ;
		("and",   fun args env -> ScmBoolean(List.fold_left ( && ) true (List.map as_CondValue args))) ;
		("or",    fun args env -> ScmBoolean(List.fold_right ( || ) (List.map as_CondValue args) false)) ;
        ("list",  fun args env -> ScmList(args)) ;
        ("cons",  fun args env -> match args with f :: [ScmList(r)] -> ScmList((f :: r)) | x -> error ("Bad args: " ^ (scmvals_to_string args))) ;
        ("car",   fun args env -> match args with [ScmList(f :: _)] -> f | x -> error ("Bad args: " ^ (scmvals_to_string args))) ; 
        ("cdr",   fun args env -> match args with [ScmList(_ :: r)] -> ScmList(r) | x -> error ("Bad args: " ^ (scmvals_to_string args))) ;
    ] in
	List.fold_left (fun env def -> let (name, f) = def in (env_put env name (ScmProc(name, f)))) 
		(List.fold_left (fun env def -> let (name, value) = def in (env_put env name value)) 
			EmptyEnv 
		syms) 
	funcs

(* (eval -> string -> scheme_env) -> (scheme_val * scheme_env) *)

let rec eval exp_str env =
	let is_list = function ScmList(_) | ScmPair(_, _) -> true | _ -> false in
	let is_atom exp = not (is_list exp) in
	let is_special exp =
		match (exp_1st exp) with 
			ScmSymbol("eval") | 
			ScmSymbol("define") | ScmSymbol("set!") | 
			ScmSymbol("quote") | ScmSymbol("'") | 
			ScmSymbol("cond") | ScmSymbol("if") |
			ScmSymbol("begin") | 
			ScmSymbol("lambda") -> true |
			_ -> false in
	let return_last exps = List.nth exps ((List.length exps) - 1) in
    (* (eval' -> scheme_val -> scheme_env) -> (scheme_val * scheme_env) *)
    let rec eval' exp env =
        (* (eval_atom -> scheme_val -> scheme_env) -> (scheme_val * scheme_env) *)
        let eval_atom exp env = 
            match exp with
                (ScmNil | ScmBoolean(_) | ScmNumber(_) | ScmString(_) | ScmProc(_, _)) as a -> (a, env) |
                ScmSymbol(s) -> let (value, found) = (env_get env s) in (value, env) |
                x -> error ("Not an Atom: " ^ (scmval_to_string x)) in
        (* (eval_seq -> scheme_val -> scheme_env) -> scheme_val list *)
        let rec eval_seq exp env =
            match exp with
                ScmList(lst) -> List.map (fun e -> (fst (eval' e env))) lst |
                x -> error ("Not a List: " ^ (scmval_to_string x)) in
        (* (eval_special -> scheme_val -> scheme_val -> scheme_env) -> (scheme_val * scheme_env) *)
        let rec eval_special exp env =
			(*** (quote [exp]) ************************************************)
			let eval_quote exp env =
				((exp_1st exp), env) in
			(*** (define [symbol] [exp]) ***************************************)
            let eval_define exp env =
                let key = as_SchmTextType (exp_1st exp) in
                let (value, env') = eval' (exp_2nd exp) env in
                    (ScmNil, (env_put env' key value)) in
			(*** (set! [symbol] [exp]) ****************************************)
			let eval_set exp env =
				let key = as_SchmTextType (exp_1st exp) in
				let (value, env') = eval' (exp_2nd exp) env in
					if (env_exists env' key) then (ScmNil, (env_put env' key value))
					else error ("Trying to set a non-existent symbol: " ^ key) in
			(*** (begin [exp]) ************************************************)
			let eval_begin exp env = ((return_last (eval_seq exp env)), env) in
			(*** (cond ************************************************)
			(* (cond ScmList([<clause0> ; <clause1>; ... ; <clauseN-1>])) *)
			let rec eval_cond exp env =
				if (exp_count exp) = 0 then (ScmNil, env)
				else
					let clause = (exp_1st exp) in
					let test = (exp_1st clause) in
					match test with
						ScmSymbol("else") -> ((return_last (eval_seq (exp_rest clause) env)), env) |
						_ -> if (as_CondValue (fst (eval' test env))) then ((return_last (eval_seq (exp_rest clause) env)), env)
							 else eval_cond (exp_rest exp) env in
			(*** (if [test] [true-exp] [false-exp] ****************************)
			let eval_if exp env =
				let test = (exp_1st exp) in
				if (as_CondValue (fst (eval' test env))) then (eval' (exp_2nd exp) env) else (eval' (exp_last exp) env) in
			(*** (lambda [arg-list] [body]) ***********************************)
			let eval_lambda exp env =
                let lambda_name = "lambda#" ^ (string_of_int (Random.int 0x00ffffff)) in
				let params = as_SchmTextTypes (as_ScmAggregateType (exp_1st exp)) in
				let body = exp_last exp in (ScmProc(lambda_name, fun args env -> fst (eval' body (env_put_many env params args))), env) in
				let first = (exp_1st exp) in
				let rest  = (exp_rest exp) in
					(* print_exp rest ; *)
					match first with
						ScmSymbol("quote")  -> (eval_quote rest env) |
						ScmSymbol("define") -> (eval_define rest env) |
						ScmSymbol("set!")   -> (eval_set rest env) |
						ScmSymbol("begin")  -> (eval_begin rest env) |
						ScmSymbol("cond")   -> (eval_cond rest env) |
						ScmSymbol("if")     -> (eval_if rest env) |
						ScmSymbol("lambda") -> (eval_lambda rest env) |
						ScmSymbol("eval")   -> (eval' (exp_1st rest) env) |
						x -> error ("Not a special form: " ^ (scmval_to_string x)) in
        (* apply -> scheme_val -> scheme_val list ->  *)
        let rec apply proc args env = 
            match proc with
                ScmProc(_, fn) -> ((fn args env), env) |
                x -> error ("Not a Proc:" ^ (scmval_to_string x)) in
			if (is_atom exp) then eval_atom exp env
			else if (is_special exp) then eval_special exp env
			else apply (fst (eval' (exp_1st exp) env)) (eval_seq (exp_rest exp) env) env in
        eval' (parse (tokenize exp_str)) env

let read_exp_from_stream stream env =
	let rec read_exp_from_stream' accum_line env =
		let stream_line =  (input_line stream) in
		(* print_endline ("stream -> " ^ stream_line) ; *)
		if (String.length stream_line) = 0 then
			begin
				print_string "> " ; 
				flush stdout ; 
				read_exp_from_stream' accum_line env
			end
		else
			let full_line = accum_line ^ stream_line in
			try 
				eval full_line env 
			with NoMoreTokens -> read_exp_from_stream' full_line env in
	read_exp_from_stream' "" env

let read_exp_from_stdin env = read_exp_from_stream stdin env

let repl () = 
    let rec repl' prompt env =
		print_string prompt ; 
		flush stdout ;
		try 
			let (exp', env') = read_exp_from_stdin env in
				print_exp exp' ;
				print_newline () ;
				repl' prompt env'
		with
			SchemeError(msg) -> 
				print_endline ("*Scheme-Error* " ^ msg) ; 
				(* Printexc.print_backtrace stdout ; *)
				repl' prompt env in
		repl' ">> " (env_init ())

let _ =
	set_binary_mode_in stdin true ; 
	repl ()
