(* =========================================================================================================== *)
structure TypeChecker =
struct

open Model;
open CONCRETE_REPRESENTATION;

(* =========================================================================================================== *)
(*
    Here is where your typeCheck and typeOf definitions go. The primary challenge here is to translate the parse 
    expression notation we used in M2 to the actual SML tree patterns used in the TL System. See the comments in
    the semantics.sml file for a more detailed discussion on this topic. 
*)

(*exception catch for errors*)
exception model_error;

(*if an error occurs this message can appear*)
fun error message = (print message, raise model_error);


(*Expr*)
fun typeOf( itree ( inode ("Expr",_),
    [
        Expr0,
        itree ( inode ( "or",_),[]),
        LogicalAnd0
    ]),
    m0
    )=
    let
        val t0 = typeOf(Expr0, m0)
        val t1 = typeOf(LogicalAnd0, m0)
    in
        if t0 = BOOL andalso t0 = t1
        then BOOL
        else ERROR
    end    
    
| typeOf ( itree ( inode ( "Expr",_),
    [
        LogicalAnd0
    ]),
    m0
    )= typeOf(LogicalAnd0, m0)
    
    
(*LogicalAnd*)
|   typeOf ( itree ( inode ( "LogicalAnd",_),
    [
        LogicalAnd0,
        itree ( inode ( "and",_),[]),
        Equality0
    ]),
    m0
    )=
    let
        val t0 = typeOf(LogicalAnd0, m0)
        val t1 = typeOf(Equality0, m0)
    in
        if t0 = BOOL andalso t0 = t1
        then BOOL
        else ERROR
    end
    
| typeOf ( itree ( inode ( "LogicalAnd",_),
    [
        Equality0
    ]),
    m0
    )= typeOf(Equality0, m0)
    
(*Equality*)
| typeOf ( itree ( inode ( "Equality",_),
    [
        Relational0,
        itree ( inode ( "=",_),[]),
        Relational1
    ]),
    m0
    )=
    let
        val t0 = typeOf(Relational0, m0)
        val t1 = typeOf(Relational1, m0)
    in
        if t1 <> ERROR andalso t0 = t1
        then BOOL
        else ERROR
    end
    
| typeOf ( itree ( inode ( "Equality",_),
    [
        Relational0,
        itree ( inode ( "!=",_), []),
        Relational1
        ]),
        m0
        )=
        let
            val t0 = typeOf(Relational0, m0)
            val t1 = typeOf(Relational1, m0)
        in
            if t1 <> ERROR andalso t0 = t1
            then BOOL
            else ERROR
        end
        
        
| typeOf ( itree ( inode ( "Equality",_),
    [
        Relational0
    ]),
    m0 )= typeOf(Relational0, m0)
    
(*Relational*)
| typeOf ( itree ( inode ( "Relational",_),
    [
        Additive0,
        itree ( inode ( "<",_),[]),
        Additive1
    ]),
    m0
    ) =
    let
        val t0 = typeOf(Additive0, m0)
        val t1 = typeOf(Additive1, m0)
    in
        if t0 = INT andalso t0 = t1
        then BOOL
        else ERROR
    end
    
| typeOf ( itree ( inode ( "Relational",_),
    [
        Additive0,
        itree ( inode ( ">",_),[]),
        Additive1
    ]),
    m0
    ) =
    let
        val t0 = typeOf(Additive0, m0)
        val t1 = typeOf(Additive1, m0)
    in
        if t0 = INT andalso t0 = t1
        then BOOL
        else ERROR
    end   
    
| typeOf ( itree ( inode ( "Relational",_),
    [
        Additive0,
        itree ( inode ( "<=",_),[]),
        Additive1
    ]),
    m0
    ) =
    let
        val t0 = typeOf(Additive0, m0)
        val t1 = typeOf(Additive1, m0)
    in
        if t0 = INT andalso t0 = t1
        then BOOL
        else ERROR
    end
    
    
| typeOf ( itree ( inode ( "Relational",_),
    [
        Additive0,
        itree ( inode ( ">=",_),[]),
        Additive1
    ]),
    m0
    ) =
    let
        val t0 = typeOf(Additive0, m0)
        val t1 = typeOf(Additive1, m0)
    in
        if t0 = INT andalso t0 = t1
        then BOOL
        else ERROR
    end    

| typeOf ( itree ( inode ( "Relational",_),
    [
        Additive0
    ]),
    m0 )= typeOf(Additive0, m0)
    

(*Additive*)
| typeOf ( itree ( inode ( "Additive",_),
    [
        Additive0,
        itree ( inode ( "+",_),[]),
        Multiplicative0
    ]),
    m0
    )=
    let
        val t0 = typeOf(Additive0, m0)
        val t1 = typeOf(Multiplicative0, m0)
    in
        if t0 = INT andalso t0 = t1
        then INT
        else ERROR
    end
    
| typeOf ( itree ( inode ( "Additive",_),
    [
        Additive0,
        itree ( inode ( "-",_),[]),
        Multiplicative0
    ]),
    m0
    )=
    let
        val t0 = typeOf(Additive0, m0)
        val t1 = typeOf(Multiplicative0, m0)
    in
        if t0 = INT andalso t0 = t1
        then INT
        else ERROR
    end
        
| typeOf( itree ( inode ("Additive",_),
    [
        Multiplicative0
    ]),
    m0 )= typeOf(Multiplicative0, m0)
    
    
    
(*Multiplicative*)
| typeOf( itree ( inode ("Multiplicative",_),
    [
        Multiplicative0,
        itree ( inode ( "*",_),[]),
        Negation0
    ]),
    m0
    )=
    let
        val t0 = typeOf(Multiplicative0, m0)
        val t1 = typeOf(Negation0, m0)
    in
        if t0 = INT andalso t0 = t1
        then INT
        else ERROR
    end
    
| typeOf( itree ( inode ("Multiplicative",_),
    [
        Multiplicative0,
        itree ( inode ( "div",_),[]),
        Negation0
    ]),
    m0
    )=
    let
        val t0 = typeOf(Multiplicative0, m0)
        val t1 = typeOf(Negation0, m0)
    in
        if t0 = INT andalso t0 = t1
        then INT
        else ERROR
    end
    
| typeOf( itree ( inode ("Multiplicative",_),
    [
        Multiplicative0,
        itree ( inode ( "mod",_),[]),
        Negation0
    ]),
    m0
    )=
    let
        val t0 = typeOf(Multiplicative0, m0)
        val t1 = typeOf(Negation0, m0)
    in
        if t0 = INT andalso t0 = t1
        then INT
        else ERROR
    end    

| typeOf ( itree ( inode ("Multiplicative",_),
    [
        Negation0
    ]),
    m0 )= typeOf(Negation0, m0)
    
    
    
(*Negation*)
| typeOf ( itree ( inode ("Negation",_),
    [
        itree ( inode ( "not",_),[]),
        Negation0
    ]),
    m0
    ) =
    let
        val t0 = typeOf(Negation0, m0)
    in
        if t0 = BOOL
        then BOOL
        else ERROR
    end
    
| typeOf ( itree ( inode ("Negation",_),
    [
        itree ( inode ("-",_),[]),
        Negation0
    ]),
    m0
    )=
    let
        val t0 = typeOf(Negation0, m0)
    in
        if t0 = BOOL
        then BOOL
        else ERROR
    end
    
    
    
(*Exponentiation*)    
| typeOf ( itree ( inode ( "Exponentiation",_),
    [
        Final0,
        itree ( inode ( "^",_),[]),
        Exponentiation0
    ]),
    m0
    )=
    let
        val t0 = typeOf(Final0, m0)
        val t1 = typeOf(Exponentiation0, m0)
    in
        if t0 = INT andalso t0 = t1
        then INT
        else ERROR
    end
    
| typeOf ( itree ( inode ( "Exponentiation",_),
    [
        Final0
    ]),
    m0 )= typeOf(Final0, m0)
        
    
(*Final*)
| typeOf ( itree ( inode ("Final",_),
    [
        itree ( inode ( "(",_),[]),
        Expr0,
        itree ( inode ( ")",_),[])
    ]),
    m0 )= typeOf( Expr0, m0)
    
| typeOf ( itree ( inode ( "Final",_),
    [
        itree ( inode ( "|",_),[]),
        Expr0,
        itree ( inode ( "|",_),[])
    ]),
    m0
    )=
    let
        val t0 = typeOf(Expr0, m0)
    in
        if t0 = INT
        then INT
        else ERROR
    end
       
| typeOf ( itree ( inode ( "Final",_),
    [
        Change0 as itree ( inode ( "Change",_), children)
    ]),
    m0 )= typeOf(Change0, m0)
    
| typeOf ( itree ( inode ( "Final",_),
    [
        Id0 as itree ( inode ( "Id",_), children)
    ]),
    m0 )= typeOf(Id0, m0)
    
| typeOf ( itree ( inode ( "Final",_),
    [
        Integer0 as itree ( inode ( "Integer",_), children)
    ]),
    m0 )= INT
    
| typeOf ( itree ( inode ( "Final",_),
    [
        Boolean0 as itree ( inode ( "true",_), children)
    ]),
    m0 )= BOOL
    
| typeOf ( itree ( inode ( "Final",_),
    [
        Boolean0 as itree ( inode ( "false",_), children)
    ]),
    m0 )= BOOL    
    
(*Pre/Post*)    
| typeOf ( itree ( inode ( "Pre_Inc",_),
    [
        itree ( inode ("++",_),[]),
        Id0
    ]),
    m0 
    )=
    let
        val t0 = getType ( accessEnv ( getLeaf ( Id0 ), m0))
    in
        if t0 = INT
        then INT
        else ERROR
    end    

| typeOf ( itree ( inode ( "Post_Inc",_),
    [
        Id0,
        itree ( inode ("++",_),[])
    ]),
    m0 
    )=
    let
        val t0 = getType ( accessEnv ( getLeaf ( Id0 ), m0))
    in
        if t0 = INT
        then INT
        else ERROR
    end  
    
| typeOf ( itree ( inode ( "Pre_Dec",_),
    [
        itree ( inode ("--",_),[]),
        Id0
    ]),
    m0 
    )=
    let
        val t0 = getType ( accessEnv ( getLeaf ( Id0 ), m0))
    in
        if t0 = INT
        then INT
        else ERROR
    end  
    
| typeOf ( itree ( inode ( "Post_Dec",_),
    [
        Id0,
        itree ( inode ("--",_),[])
    ]),
    m0 
    )=
    let
        val t0 = getType ( accessEnv ( getLeaf ( Id0 ), m0))
    in
        if t0 = INT
        then INT
        else ERROR
    end      
    
    
    
        
        
        
        
        
        
        
(*Program or prog*)
fun typeCheck( itree ( inode("Program",_),
    [
        Statement_List0
    ]),
    m0
    ) = typeCheck(Statement_List0, m0)
    
    (*Statement List*)
|   typeCheck( itree ( inode("Statement_List",_),
    [
        Statement0,
        itree ( inode ( ";",_), []),
        Statement_List0
    ]),
    m0
    ) = 
        let 
        val m1 = typeCheck(Statement0, m0)
        val m2 = typeCheck(Statement_List0, m1)
    in
        m2
    end
    
(*Statement options*)
| typeCheck( itree ( inode ( "Statement",_),
    [
        Init0 as itree ( inode ( "Init",_), children)
    ]),
    m0
    )= typeCheck( Init0, m0)

| typeCheck( itree ( inode ( "Statement",_),
    [
        Assign0 as itree ( inode ( "Assign",_), children)
    ]),
    m0
    )= typeCheck( Assign0, m0)
    
| typeCheck( itree ( inode ( "Statement",_),
    [
        Decl0 as itree ( inode ( "Decl",_), children)
    ]),
    m0
    )= typeCheck( Decl0, m0)
    
| typeCheck( itree ( inode ( "Statement",_),
    [
        Block0 as itree ( inode ( "Block",_), children)
    ]),
    m0
    )= typeCheck( Block0, m0)
    
| typeCheck( itree ( inode ( "Statement",_),
    [
        For_Loop0 as itree ( inode ( "For_loop",_), children)
    ]),
    m0
    )= typeCheck( For_Loop0, m0)
    
| typeCheck( itree ( inode ( "Statement",_),
    [
        While_Loop0 as itree ( inode ( "While_Loop",_), children)
    ]),
    m0
    )= typeCheck( While_Loop0, m0)
    
| typeCheck( itree ( inode ( "Statement",_),
    [
        Branch0 as itree ( inode ( "Branch",_), children)
    ]),
    m0
    )= typeCheck( Branch0, m0)
    
| typeCheck( itree ( inode ( "Statement",_),
    [
        Change0 as itree ( inode ( "Change",_), children)
    ]),
    m0
    )= typeCheck( Change0, m0)
    
| typeCheck( itree ( inode ( "Statement",_),
    [
        Print_Expr as itree ( inode ( "Print_Expr",_), children)
    ]),
    m0
    )= typeCheck( Print_Expr, m0)
    
    
 (*Init*)   
| typeCheck ( itree ( inode ( "Init",_),
    [
        itree ( inode ( "integer",_), []),
        Id0,
        itree ( inode ( ":=",_), []),
        Expr0
    ]),
    m0
    ) =    
    let 
        val m1 = updateEnv ( getLeaf( Id0), INT, 0, m0)
        val t0 = typeOf (Expr0, m0)
    in
        if t0 = INT
        then m1
        else raise model_error
    end    
    
| typeCheck ( itree ( inode ( "Init",_),
    [
        itree ( inode ( "bool",_), []),
        Id0,
        itree ( inode ( ":=",_), []),
        Expr0
    ]),
    m0
    )=
    let 
        val m1 = updateEnv ( getLeaf( Id0), BOOL, 0, m0)
        val t0 = typeOf (Expr0, m0)
    in
        if t0 = BOOL
        then m1
        else raise model_error
    end  
    
    
(*Assign*)    
| typeCheck ( itree ( inode ( "Assign",_),
    [
        Id0,
        itree ( inode ( ":=",_), []),
        Expr0
    ]),
    m0
    ) =
    let 
        val t0 = getType( accessEnv( getLeaf ( Id0), m0))
        val t1 = typeOf (Expr0, m0)
    in
        if t0 = t1
        then m0
        else raise model_error
    end    
    
(*Decl*)    
| typeCheck ( itree ( inode ("Decl",_),
    [
        itree ( inode ("INTEGER",_), []),
        Id0
    ]),
    m0 
    ) = updateEnv( getLeaf (Id0), INT, 0, m0) 
        
| typeCheck ( itree ( inode ("Decl",_),
    [
        itree ( inode ("BOOLEAN",_), []),
        Id0
    ]),
    m0 
    ) = updateEnv( getLeaf (Id0), BOOL, 0, m0)         
    
    
    (*Id = Identifier*)
    
    
| typeCheck ( itree ( inode ( "Id",_),
    [
        Id0,
        itree ( inode ( "=",_),[]),
        Identifier0
    ]),
    m0 
    )= 
    let 
        val t0 = getType( accessEnv( getLeaf ( Id0), m0))
        val t1 = typeOf (Identifier0, m0)
    in    
        if t0 = t1
        then m0
        else raise model_error
    end 
    
    
    
    
    
 (*Block*)   
| typeCheck ( itree ( inode ( "Block",_),
    [
        itree ( inode ("{",_), []),
        Statement_List0,
        itree ( inode ( "}",_), [])
    ]),
    m0
    )=
    let
        val (env0,n0, s0) = m0
        val (env1, n1, s1) = typeCheck(Statement_List0, m0)
    in
        (env0, n0, s1)
    end    
    
(*For_Loop*)
| typeCheck ( itree ( inode ("For_Loop",_),
    [
        itree ( inode ( "for",_),[]),
        itree ( inode ( "(",_),[]),
        Init0,
        itree ( inode ( ";",_),[]),
        Expr0,
        itree ( inode ( ";",_),[]),
        Change0,
        itree ( inode ( ")",_),[]),
        Block0
        ]),
    m0
    )=
    let
        val m1 = typeCheck(Init0, m0)
        val t = typeOf(Expr0, m1)
        val m2 = typeOf(Change0, m1)
        val m3 = typeCheck(Block0, m1)
    in
        if t = BOOL
        then m1
        else raise model_error
    end
    
| typeCheck ( itree ( inode ("For_Loop",_),
    [
        itree ( inode ( "for",_),[]),
        itree ( inode ( "(",_),[]),
        Init0,
        itree ( inode ( ";",_),[]),
        Expr0,
        itree ( inode ( ";",_),[]),
        Assign0,
        itree ( inode ( ")",_),[]),
        Block0
        ]),
    m0
    )=
    let
        val m1 = typeCheck(Init0, m0)
        val t = typeOf(Expr0, m1)
        val m2 = typeOf(Assign0, m1)
        val m3 = typeCheck(Block0, m1)
    in
        if t = BOOL
        then m1
        else raise model_error
    end    
    
(*While_Loop*)
| typeCheck ( itree ( inode ("While_Loop",_),
    [
        itree ( inode ( "While",_),[]),
        itree ( inode ( "(",_),[]),
        Expr0,
        itree ( inode ( ")",_),[]),
        Block0
    ]),
    m0
    )=
    let
        val t0 = typeOf(Expr0, m0)
        val t1 = typeCheck(Block0, m0)
    in
        if t0 = BOOL
        then m0
        else raise model_error
    end
    
(*Branch*)
| typeCheck ( itree ( inode ("Branch",_),
    [
        itree ( inode ( "if",_),[]),
        Expr0,
        itree ( inode ( "then",_),[]),
        Block0
    ]),
    m0
    )=
    let
        val t0 = typeOf(Expr0, m0)
        val t1 = typeCheck(Block0, m0)
    in
        if t0 = BOOL
        then m0
        else raise model_error
    end    
        
| typeCheck ( itree ( inode ("Branch",_),
    [
        itree ( inode ( "if",_),[]),
        Expr0,
        itree ( inode ( "then",_),[]),
        Block0,
        itree ( inode ( "else",_),[]),
        Block1
    ]),
    m0
    )=
    let
        val t0 = typeOf(Expr0, m0)
        val t1 = typeCheck(Block0, m0)
        val t2 = typeCheck(Block1, m0)
    in
        if t0 = BOOL
        then m0
        else raise model_error
    end    
    
(*Print_Expr*)
| typeCheck ( itree ( inode ( "Print_Expr",_),
    [
        itree ( inode ( "print",_),[]),
        Expr0
    ]),
    m0
    )= 
    let
        val t0 = typeOf(Expr0, m0)
    in
        if t0 = ERROR
        then raise model_error
        else m0
    end
    
    
(*Change*)
| typeCheck ( itree ( inode ( "Change" ,_),
    [
            Pre_Inc0 as itree ( inode ( "Pre_Inc",_), children)
    ]),
    m0
    )= typeCheck( Pre_Inc0, m0)
        
| typeCheck ( itree ( inode ( "Change" ,_),
    [
            Post_Inc0 as itree ( inode ( "Post_Inc",_), children)
    ]),
    m0
    )= typeCheck( Post_Inc0, m0)
    
| typeCheck ( itree ( inode ( "Change" ,_),
    [
            Pre_Dec0 as itree ( inode ( "Pre_Dec",_), children)
    ]),
    m0
    )= typeCheck( Pre_Dec0, m0)

| typeCheck ( itree ( inode ( "Change" ,_),
    [
            Post_Dec0 as itree ( inode ( "Post_Dec",_), children)
    ]),
    m0
    )= typeCheck( Post_Dec0, m0)
                    
(*fun typeCheck( itree(inode("prog",_), [ stmt_list ] ), m) = m*)


  | typeCheck( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn typeCheck root = " ^ x_root ^ "\n\n")
  | typeCheck _ = raise Fail("Error in Model.typeCheck - this should never occur")


(* =========================================================================================================== *)  
end (* struct *)
(* =========================================================================================================== *)








