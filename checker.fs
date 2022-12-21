//
// Analyzer for simple C programs.  This component performs
// type checking.  The analyzer returns a string denoting
// success or failure. The string "success" if the input 
// program is legal, otherwise the string "type_error: ..." 
// is returned denoting an invalid simple C program.
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

module checker =
  //
  // NOTE: all functions in the module must be indented.
  //
    let private matchToken (expected_token: string) (tokens: string list) =
        let next_token = List.head tokens

        if expected_token = "identifier" && next_token.StartsWith("identifier") then
            List.tail tokens
        elif expected_token = "int_literal" && next_token.StartsWith("int_literal") then
            List.tail tokens
        elif expected_token = "real_literal" && next_token.StartsWith("real_literal") then
            List.tail tokens
        elif expected_token = "str_literal" && next_token.StartsWith("str_literal") then
            List.tail tokens
        elif expected_token = next_token then  
            List.tail tokens
        else
            List.tail tokens


    let rec private expr_value tokens theSymbolTable =
        let next_token = List.head tokens
        if next_token = "false" then
            let T2 = matchToken "false" tokens
            (T2, "bool")
        elif next_token = "true" then
            let T2 = matchToken "true" tokens
            (T2, "bool")
        elif next_token.StartsWith("identifier") then
            let theName = next_token.[11..]
            let doesExist = List.exists (fun(name, theType) -> name = theName) theSymbolTable
            if doesExist = false then
                failwith ("variable '" + theName + "' undefined")
            let isType = List.filter (fun(name, theType) -> name = theName) theSymbolTable
            let (name, theType) = List.head isType
            let T2 = matchToken "identifier" tokens
            (T2, theType)
        elif next_token.StartsWith("int_literal") then
            let T2 = matchToken "int_literal" tokens
            (T2, "int")
        elif next_token.StartsWith("real_literal") then
            let T2 = matchToken "real_literal" tokens
            (T2, "real")
        elif next_token.StartsWith("str_literal") then
            let T2 = matchToken "str_literal" tokens
            (T2, "str")
        else
            let T2 = List.tail tokens
            (T2, "")

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

    let private properOperators (firstIdent : string) (firstType : string) (secondIdent : string) (secondType : string) (theOP : string) theSymbolTable =
        if (firstIdent.StartsWith("identifier") && secondIdent.StartsWith("identifier")) then
            if not(firstType.Equals("int") || firstType.Equals("real")) || not(secondType.Equals("int") || secondType.Equals("real")) then
                failwith ("operator " + theOP + " must involve 'int' or 'real'")
            if not(firstType.Equals(secondType)) then
                failwith ("type mismatch '" + firstType + "' " + theOP + " '" + secondType + "'")
        elif firstIdent.StartsWith("identifier") then
            if not(firstType.Equals("int") || firstType.Equals("real")) then
                failwith ("operator " + theOP + " must involve 'int' or 'real'")
            if not(secondType.Equals("int") || secondType.Equals("real")) then
                failwith ("operator " + theOP + " must involve 'int' or 'real'")
            if secondType.Equals("int") && firstType <> "int" then
                failwith("type mismatch '" + firstType + "' " + theOP + " 'int'")
            if secondType.Equals("real") && firstType <> "real" then
                failwith ("type mismatch '" + firstType + "' " + theOP + " 'real'")
        elif secondIdent.StartsWith("identifier") then
            if not(secondType.Equals("int") || secondType.Equals("real")) then
                failwith ("operator " + theOP + " must involve 'int' or 'real'")
            if not(firstType.Equals("int") || firstType.Equals("real")) then
                failwith ("operator " + theOP + " must involve 'int' or 'real'")
            if firstType.Equals("int") && secondType <> "int" then
                failwith ("type mismatch 'int' " + theOP + " '" + secondType + "'")
            if firstType.Equals("real") && secondType <> "real" then
                failwith ("type mismatch 'real' " + theOP + " '" + secondType + "'")
        elif firstType.Equals("str") || secondType.Equals("str") || firstType.Equals("bool") || secondType.Equals("bool") then
            failwith("operator " + theOP + " must involve 'int' or 'real'")
        

    let rec private expr tokens theSymbolTable =
        let(T2, firstType) = expr_value tokens theSymbolTable
        let firstIdent = List.head tokens
        let next_token = List.head T2
        if (next_token = "+" || next_token = "-" || next_token = "*" || next_token = "/" || next_token = "^") then
            let T3 = expr_op T2
            let secondIdent = List.head T3
            let (T4, secondType) = expr_value T3 theSymbolTable
            properOperators firstIdent firstType secondIdent secondType next_token theSymbolTable
            if (firstType.Equals(secondType)) then
                (T4, firstType)
            else 
                (T4, "either")

        elif (next_token = "<"  || next_token = "<=" || next_token = ">"  || next_token = ">=" || next_token = "==" || next_token = "!=") then
            let T3 = expr_op T2
            let secondIdent = List.head T3
            let (T4, secondType) = expr_value T3 theSymbolTable
            if firstType.Equals(secondType) && (firstType = "bool" || firstType = "int" || firstType = "real" || firstType = "str") then
                if firstType.Equals(secondType) && firstType = "real" && next_token = "==" then
                    printfn "warning: comparing real numbers with == may never be true"
                (T4, "bool")
            else
                failwith("type mismatch '" + firstType + "' " + next_token + " '" + secondType + "'")
        else
            (T2, firstType)

    let rec private empty tokens =
        let T2 = matchToken ";" tokens
        T2

    let rec private vardecl tokens = 
        if (List.head tokens = "int") then
            let T2 = matchToken "int" tokens
            let T3 = matchToken "identifier" T2
            let T4 = matchToken ";" T3
            T4
        elif (List.head tokens = "real") then
            let T2 = matchToken "real" tokens
            let T3 = matchToken "identifier" T2
            let T4 = matchToken ";" T3
            T4
        else
            failwith ("redefinition of variable '" + (List.head tokens) + "'")

    let rec private input tokens theSymbolTable =
        let T2 = matchToken "cin" tokens
        let T3 = matchToken ">>" T2
        let theName = (List.head T3).[11..]
        let doesExist = List.exists (fun(name, theType) -> name = theName) theSymbolTable
        if doesExist = false then
            failwith ("variable '" + theName + "' undefined")
        let T4 = matchToken "identifier" T3
        let T5 = matchToken ";" T4
        T5

    let rec private output_value tokens theSymbolTable =
        let next_token = List.head tokens
        if next_token = "endl" then
            let T2 = matchToken "endl" tokens
            T2
        else
            let (T2, t1) = expr_value tokens theSymbolTable
            T2

    let rec private output tokens theSymbolTable = 
        let T2 = matchToken "cout" tokens
        let T3 = matchToken "<<" T2
        let T4 = output_value T3 theSymbolTable
        let T5 = matchToken ";" T4
        T5

    let private theVariableName (name : string) =
        let theName = name.[11..]
        theName

    let rec private assignment tokens theSymbolTable =
        let theName = theVariableName (List.head tokens)
        let doesExist = List.exists (fun(name, theType) -> name = theName) theSymbolTable
        if doesExist = false then
            failwith ("variable '" + theName + "' undefined")
        let isType = List.filter (fun(name, firstType) -> name = theName) theSymbolTable
        let (name, firstType) = List.head isType
        let T2 = matchToken "identifier" tokens
        let T3 = matchToken "=" T2
        let (T4, secondType) = expr T3 theSymbolTable
        if (firstType <> "real" || secondType <> "int") && (firstType <> secondType) then
            failwith("cannot assign '" + secondType + "' to variable of type '" + firstType + "'")
        let T5 = matchToken ";" T4
        T5

    let rec private stmt tokens theSymbolTable = 
        let next_token = List.head tokens
        if next_token = ";" then
          let T2 = empty tokens
          T2
        elif next_token = "int" then
          let T2 = vardecl tokens
          T2
        elif next_token = "real" then
          let T2 = vardecl tokens
          T2
        elif next_token = "cin" then
          let T2 = input tokens theSymbolTable
          T2
        elif next_token = "cout" then
          let T2 = output tokens theSymbolTable
          T2
        elif next_token.StartsWith("identifier") then
          let T2 = assignment tokens theSymbolTable
          T2
        elif next_token = "if" then
          let T2 = ifstmt tokens theSymbolTable
          T2
        else
          failwith ("expecting statement, but found " + next_token)

    and private ifstmt tokens theSymbolTable =
        let T2 = matchToken "if" tokens
        let T3 = matchToken "(" T2
        let (T4, t1) = condition T3 theSymbolTable
        if not(t1.Equals("bool")) then
            failwith("if condition must be 'bool', but found '" + t1 + "'")
        let T5 = matchToken ")" T4
        let T6 = then_part T5 theSymbolTable
        let T7 = else_part T6 theSymbolTable
        T7

    and private condition tokens theSymbolTable =
        let (T2, t1) = expr tokens theSymbolTable
        (T2, t1)

    and private then_part tokens theSymbolTable = 
        let T2 = stmt tokens theSymbolTable
        T2

    and private else_part tokens theSymbolTable = 
        let next_token = List.head tokens
        if next_token = "else" then
          let T2 = matchToken "else" tokens
          let T3 = stmt T2 theSymbolTable
          T3
        else
          tokens

    let rec private morestmts (tokens: string list)  theSymbolTable =
        let next_token = List.head tokens
        if  next_token = ";" ||
            next_token = "int"  ||
            next_token = "real" ||
            next_token = "cin"  ||
            next_token = "cout" ||
            next_token.StartsWith("identifier") ||
            next_token = "if" then
                let T2 = stmt tokens theSymbolTable
                let T3 = morestmts T2 theSymbolTable
                T3
        else 
            tokens

    let rec private stmts tokens theSymbolTable = 
        let T2 = stmt tokens theSymbolTable
        let T3 = morestmts T2 theSymbolTable
        T3

    
    let private simpleC tokens symboltable = 
        let T2 = matchToken "void" tokens
        let T3 = matchToken "main" T2
        let T4 = matchToken "(" T3
        let T5 = matchToken ")" T4
        let T6 = matchToken "{" T5
        let T7 = stmts T6 symboltable
        let T8 = matchToken "}" T7
        let T9 = matchToken "$" T8
        T9

  //
  // typecheck tokens symboltable
  //
  // Given a list of tokens and a symbol table, type-checks 
  // the program to ensure program's variables and expressions
  // are type-compatible. If the program is valid, returns 
  // the string "success". If the program contains a semantic
  // error or warning, returns a string of the form
  // "type_error: ...".
  //
    let typecheck tokens symboltable = 
        try
            let T2 = simpleC tokens symboltable
            "success"
        with 
            | ex -> "type_error: " + ex.Message
    
