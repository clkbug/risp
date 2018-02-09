open ScanRat
open System.Security.Cryptography.X509Certificates

type Exp =
    | Symbol of string
    | Cons of Exp * Exp
    | Fun of Env * (string list) * Exp
and Env = Map<string, Exp>

let nil = Symbol("nil")
let t = Symbol("t")
let initEnv = Map.empty |> Map.add "nil" (nil)

let parse s =
    let tfold name x d f g =
        let a = production name
        a.rule
          <- a + x --> f
          |- d --> g
        a
    let tfold' name x d f = tfold name x d f id
    let tfold_d name x f = tfold' name x x f
    let add = fun (x, y) -> x + y

    let spaces = tfold' "spaces" ~~" " ~~"" add
    let ss x = spaces +. x .+ spaces

    let char = oneOf "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_!#$%&-=~^|+*?" --> fun c -> c.ToString()
    let str = tfold_d "str" char add
    let sym = ss str --> fun s -> Symbol(s)
    let innerList = production "innerList"
    let list = ss ~~"(" +. innerList .+ ss ~~")" --> id
    let exp = production "exp"
    exp.rule <- list |- sym 
      |- ~~"'" +. exp --> fun x -> Cons(Symbol("quote"), Cons(x, nil))
    innerList.rule
      <- exp + innerList --> fun (x, y) -> Cons(x, y)
      |- exp --> fun x -> Cons(x, nil)
      |- ~~"" --> fun _ -> nil
    
    parse exp s
   
let rec consFold f acc = function
    | Symbol("nil") -> acc
    | Cons(x, xs) -> consFold f (f acc x) xs
    | _ -> failwith "can't fold dotpair"

let rec eval (env : Env) exp =
    match exp with
    | Symbol(s) -> env, Map.find s env
    | Cons(Symbol("quote"), Cons(xs, _)) -> env, xs
    | Cons(Symbol("if"), Cons(p, Cons(t, f))) ->
        let _, p = eval env p
        if p = Symbol("t")
        then eval env t
        else match f with
             | Cons(f, _) -> eval env f
             | Symbol("nil") -> env, nil
             | _ -> failwith "can't reach here"
    | Cons(Symbol("lambda"), Cons(args, Cons(body, _))) ->
        let getStr =
            function
            | Symbol(x) -> x
            | x -> failwithf "can't get string from %A" x
        let args' = consFold (fun acc x -> getStr x :: acc) [] args |> List.rev
        env, Fun(env, args', body)
    | Cons(Symbol("define"), Cons(Symbol(name), Cons(body, _))) ->
        let env', body' = eval env body
        let env'' = Map.add name body' env'
        env'', nil
    | _ -> env, apply env exp
and apply (env : Env) = function
    | Cons(func, args) ->
        let args' = consFold (fun acc x -> let _, x' = eval env x in x' :: acc) [] args |> List.rev
        match func with
        | Symbol("atom") ->
            match List.head args' with
            | Symbol(_) -> t
            | _ -> nil
        | Symbol("eq") ->
            match args' with
            | x::y::_ -> if x = y then t else nil
            | _ -> nil
        | Symbol("car") ->
            match List.head args' with
            | Cons(x, _) -> x
            | _ -> failwith "can't apply car"
        | Symbol("cdr") ->
            match List.head args' with
            | Cons(_, x) -> x
            | _ -> failwith "can't apply cdr"
        | Symbol("cons") -> Cons(List.head args', List.head (List.tail args'))
        | Symbol(x) -> let f = Map.find x env in apply env (Cons(f, args))
        | Fun(c, a, b) ->
            let env' = List.zip a args' |> List.fold (fun x (k, v) -> Map.add k v x) c
            let _, res = eval env' b
            res
        | _ -> let _, f = eval env func in apply env (Cons(f, args))
    | _ -> failwith "can't apply"
    
[<EntryPoint>]
let main argv = 
    let getInput () = printf "> "; System.Console.ReadLine()
    let rec loop e t =
        match t with
        | "" -> ()
        | _ ->
            match parse t with
            | Failure(f) -> printfn "parse fail:\n%A" f; loop e (getInput())
            | Success(exp) ->
                let e', r = eval e exp.value
                printfn "%A" r
                loop e' (getInput ())
    loop initEnv (getInput())
    System.Console.ReadLine() |> fun _ -> 0
