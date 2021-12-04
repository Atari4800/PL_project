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

exception model_error;

fun error message = (print message, raise model_error);

(*Program or prog*)
fun typeCheck( itree ( inode("prog",_),
    [
        Statement_List0
    ]),
    m0
    ) = typeCheck(Stmt0, m0)
    
    (*Statement List*)
|   typeCheck( itree ( inode("Statement_List",_),
    [
        Stmt0,
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
        itree ( inode ( "INTEGER",_), []),
        Id0
        itree ( inode ( "=",_), []),
        Expr0
    ]),
    m0
    ) =    
    let 
        val m1 = updateEnv ( getLeaf( Id0), INT, m0)
        val t0 = typeOf (Expr0, m0)
    in
        if t0 = INT
        then m1
        else raise model_error
    end    
    
| typeCheck ( itree ( inode ( "Init",_),
    [
        Id0
        itree ( inode ( "=",_), []),
        Expr0
    ]),
    m0
    ) =    
    
    
(*Assign*)    
| typeCheck ( itree ( inode ( "Assign",_),
    [
        Id0
        itree ( inode ( "=",_), []),
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
        else error "Error: Incorrect Assignment"
    end    
    
(*Decl*)    
| typeCheck ( itree ( inode ("Decl",_),
    [
        itree ( inode ("INTEGER",_), []),
        Id0;
    ]),
    m0 
    ) = updateEnv( getLeaf (Id0), INT, m0) 
        
| typeCheck ( itree ( inode ("Decl",_),
    [
        itree ( inode ("BOOLEAN",_), []),
        Id0;
    ]),
    m0 
    ) = updateEnv( getLeaf (Id0), BOOL, m0)         
    
    
    (*Id = Identifier*)
    
    
    
    
    
    
    
    
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
| typeCheck ( itree ( inode ("For_Loop"),_),
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
    
| typeCheck ( itree ( inode ("For_Loop"),_),
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
| typeCheck ( itree ( inode ("While_Loop"),_),
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
| typeCheck ( itree ( inode ("Branch"),_),
    [
        itree ( inode ( "if",_),[]),
        Expr0
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
        
| typeCheck ( itree ( inode ("Branch"),_),
    [
        itree ( inode ( "if",_),[]),
        Expr0
        itree ( inode ( "then",_),[]),
        Block0
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
    
(*Change*)

(*Pre/Post stuff*)


    
            
(*fun typeCheck( itree(inode("prog",_), [ stmt_list ] ), m) = m*)


  | typeCheck( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn typeCheck root = " ^ x_root ^ "\n\n")
  | typeCheck _ = raise Fail("Error in Model.typeCheck - this should never occur")


(* =========================================================================================================== *)  
end (* struct *)
(* =========================================================================================================== *)








