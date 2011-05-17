//  /*--------------------------------------------------------*\
//  |   Main Program: Test Driver for BL Tokenizing Machine
//  |*--------------------------------------------------------*|
//  |   Date:
//  |   Author:
//  |
//  |   Brief User's Manual:
//  |   Allows user to test an implementation of the 
//  |   BL Tokenizing Machine with input done by redirection.
//  |
//  \*--------------------------------------------------------*/

///-------------------------------------------------------------
/// Global Context ---------------------------------------------
///-------------------------------------------------------------

#include "RESOLVE_Foundation.h"

#include "CI/BL_Tokenizing_Machine/1_C.h"

///-------------------------------------------------------------
/// Global operations ------------------------------------------
///-------------------------------------------------------------

global_function Text Kind_Name (
	preserves Integer token_kind
    );

///-------------------------------------------------------------
/// Global operation bodies ------------------------------------
///-------------------------------------------------------------

function_body Text Kind_Name (
	preserves Integer token_kind
    )
{
    case_select (token_kind)
    {
	case KEYWORD:
	{
	    return "KEYWORD         ";
	}
	break;

        case IDENTIFIER:
	{
	    return "IDENTIFIER      ";
	}
	break;

        case CONDITION:
	{
	    return "CONDITION       ";
	}
	break;

        case WHITE_SPACE:
	{
	    return "WHITE_SPACE     ";
	}
	break;

        case COMMENT:
	{
	    return "COMMENT         ";
	}
	break;

        case ERROR:
	{
	    return "ERROR           ";
	}
	break;
    }
}
    
///-------------------------------------------------------------
/// Interface --------------------------------------------------
///-------------------------------------------------------------

program_body main ()
{

    object BL_Tokenizing_Machine_1_C m;
    object Character_OStream outs;
    object Character_IStream ins;
    object Character ch;
    object Text token_text, kind_name;
    object Integer token_kind;

    ins.Open_External ("");
    outs.Open_External ("");
    outs << "Running the test case . . .\n\n";
    outs << "TOKEN KIND      TOKEN TEXT\n"
	 << "----------      ----------\n";

    while (not ins.At_EOS ())
    {
	ins.Read (ch);
	m.Insert (ch);

	if (m.Is_Ready_To_Dispense ())
	{
	    m.Dispense (token_text, token_kind);
	    kind_name = Kind_Name (token_kind);
	    outs << kind_name << '<' << token_text << ">\n";
	}
    }

    m.Flush_A_Token (token_text, token_kind);
    kind_name = Kind_Name (token_kind);
    outs << kind_name << '<' << token_text << ">\n";

    outs << "\nTest case completed.\n";
     
    ins.Close_External ();
    outs.Close_External ();
}
