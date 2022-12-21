//
// Analyzer for simple C programs.  This component performs
// semantic analysis, in particular collecting variable
// names and their types. The analysis also checks to ensure
// variable names are unique --- no duplicates.
//
// If all is well, a "symbol table" is built and returned,
// containing all variables and their types. A symbol table
// is a list of tuples of the form (name, type).  Example:
//
//   [("x", "int"); ("y", "int"); ("z", "real")]
//
// Modified by:
//   << Deep Patel >>
//
// Original author:
//   Prof. Joe Hummel
//   U. of Illinois, Chicago
//   CS 341, Spring 2022
//

namespace compiler

module analyzer =
  //
  // NOTE: all functions in the module must be indented.
  //
    let private matchToken expected_token (tokens: string list) =
        List.tail tokens


    let rec private expr_value tokens =
        List.tail tokens

    let rec private expr_op tokens = 
        let next_token = List.head tokens
        if next_token = "+"  ||
           next_token = "-"  ||
           next_token = "*"  ||
           next_token = "/"  ||
           next_token = "^"  ||
           next_token = "<"  ||
           next_token = "<=" ||
           next_token = ">"  ||
           next_token = ">=" ||
           next_token = "==" ||
           next_token = "!=" then
            let T2 = matchToken next_token tokens
            T2
        else
            List.tail tokens


    let rec private expr tokens = 
        let T2 = expr_value tokens
        let next_token = List.head T2
        if next_token = "+"  ||
           next_token = "-"  ||
           next_token = "*"  ||
           next_token = "/"  ||
           next_token = "^"  ||
           next_token = "<"  ||
           next_token = "<=" ||
           next_token = ">"  ||
           next_token = ">=" ||
           next_token = "==" ||
           next_token = "!=" then
            let T3 = expr_op T2
            let T4 = expr_value T3
            T4
        else
            T2

    let rec private empty tokens =
        let T2 = matchToken ";" tokens
        T2


    let rec private vardecl tokens theSymbolTable = 
        if (List.head tokens = "int") then
            let T2 = matchToken "int" tokens
            let next_token = List.head T2
            let T3 = matchToken "identifier" T2
            let T4 = matchToken ";" T3
            let theName = "" + next_token.[11..]
            List.iter (fun (name, theType) ->
            if (name = theName) then
                failwith("redefinition of variable '" + theName + "'")) theSymbolTable
            let theTuple = (theName, "int")
            (T4, theTuple::theSymbolTable)
        else
            let T2 = matchToken "real" tokens
            let next_token = List.head T2
            let T3 = matchToken "identifier" T2
            let T4 = matchToken ";" T3
            let theName = "" + next_token.[11..]
            List.iter (fun (name, theType) ->
            if (name = theName) then
                failwith("redefinition of variable '" + theName + "'")) theSymbolTable
            let theTuple = (theName, "real")
            (T4, theTuple::theSymbolTable)

    let rec private input tokens = 
        let T2 = matchToken "cin" tokens
        let T3 = matchToken ">>" T2
        let T4 = matchToken "identifier" T3
        let T5 = matchToken ";" T4
        T5

    let rec private output_value tokens = 
        let next_token = List.head tokens
        if next_token = "endl" then
            let T2 = matchToken "endl" tokens
            T2
        else
            let T2 = expr_value tokens
            T2

    let rec private output tokens = 
        let T2 = matchToken "cout" tokens
        let T3 = matchToken "<<" T2
        let T4 = output_value T3
        let T5 = matchToken ";" T4
        T5

    let rec private assignment tokens = 
        let T2 = matchToken "identifier" tokens
        let T3 = matchToken "=" T2
        let T4 = expr T3
        let T5 = matchToken ";" T4
        T5

    let rec private stmt tokens theSymbolTable = 
        let next_token = List.head tokens
        if next_token = ";" then
            let T2 = empty tokens
            (T2, theSymbolTable)
        elif next_token = "int" then
            let (T2, theSymbolTable) = vardecl tokens theSymbolTable
            (T2, theSymbolTable)
        elif next_token = "real" then
            let (T2, theSymbolTable) = vardecl tokens theSymbolTable
            (T2, theSymbolTable)
        elif next_token = "cin" then
            let T2 = input tokens
            (T2, theSymbolTable)
        elif next_token = "cout" then
            let T2 = output tokens
            (T2, theSymbolTable)
        elif next_token.StartsWith("identifier") then
            let T2 = assignment tokens
            (T2, theSymbolTable)
        elif next_token = "if" then
            let (T2, theTable) = ifstmt tokens theSymbolTable
            (T2, theTable)
        else
            let theTail = List.tail tokens
            (theTail, theSymbolTable)

    and private ifstmt tokens theSymbolTable = 
        let T2 = matchToken "if" tokens
        let T3 = matchToken "(" T2
        let (T4, theTable1) = condition T3
        let T5 = matchToken ")" T4
        let (T6, theTable2) = then_part T5 theSymbolTable
        let (T7, theTable3) = else_part T6 theTable2
        (T7, theTable3)

    and private condition tokens = 
        let T2 = expr tokens
        (T2, [])

    and private then_part (tokens: string list) theSymbolTable = 
        let (T2, theTable) = stmt tokens theSymbolTable
        (T2, theTable)

    and private else_part (tokens: string list) theSymbolTable = 
        let next_token = List.head tokens
        if next_token = "else" then
          let T2 = matchToken "else" tokens
          let (T3, theTable) = stmt T2 theSymbolTable
          (T3, theTable)
        else
          (tokens, theSymbolTable)

    let rec private morestmts tokens theSymbolTable = 
        let next_token = List.head tokens
        if  next_token = ";" ||
            next_token = "int"  ||
            next_token = "real" ||
            next_token = "cin"  ||
            next_token = "cout" ||
            next_token.StartsWith("identifier") ||
            next_token = "if" then
            let (T2, theTable2) = stmt tokens theSymbolTable
            let (T3, theTable3) = morestmts T2 theTable2
            (T3, theTable3)
        else 
            (tokens, theSymbolTable)

    let rec private stmts tokens theSymbolTable = 
        let (T2, theTable2) = stmt tokens theSymbolTable
        let (T3, theTable3) = morestmts T2 theTable2
        (T3, theTable3)
    

    let private simpleC tokens =
        let T2 = matchToken "void" tokens
        let T3 = matchToken "main" T2
        let T4 = matchToken "(" T3
        let T5 = matchToken ")" T4
        let T6 = matchToken "{" T5
        let (T7, theSymbolTable) = stmts T6 []
        let T8 = matchToken "}" T7
        let T9 = matchToken "$" T8
        (T9, theSymbolTable)


  //
  // build_symboltable tokens
  //
  // Given a list of tokens, analyzes the program by looking
  // at variable declarations and collecting them into a
  // list. This list is known as a symbol table. Returns
  // a tuple (result, symboltable), where result is a string 
  // denoting "success" if valid, otherwise a string of the 
  // form "semantic_error:...".
  //
  // On success, the symboltable is a list of tuples of the
  // form (name, type), e.g. [("x","int"); ("y","real")]. On 
  // an error, the returned list is empty [].
  //
    let build_symboltable tokens = 
        try
            let (T2, symboltable) = simpleC tokens
            ("success", symboltable)
        with 
            | ex -> ("semantic_error: " + ex.Message, [])
