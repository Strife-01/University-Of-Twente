package nl.utwente.jmlplugin.annotator;

import com.intellij.psi.PsiElement;
import com.intellij.psi.PsiExpression;
import com.intellij.psi.PsiType;
import nl.utwente.jmlplugin.psi.*;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.HashMap;
import java.util.Map;

/**
 * Class that holds all the error messages that can be displayed to the user by the plugin
 */
public final class ErrorMessages {
    // Syntax error messages
    public static final String SIGNALS_WITHOUT_PARENS = "A signals clause must have parentheses around the exception type";
    public static final String SQUARE_BRACKET_BUT_NOT_STAR = "Only '*' in between the square brackets is supported";
    public static final String EXCEPTION_REFERENCE_EXPECTED = "Reference(s) to one or more exceptions expected";
    public static final String NO_MODIFIER_BEFORE_SPEC = "All specification cases must be placed before any modifiers";
    public static final String NO_PARENS_AROUND_QUANTIFIER = "A quantified expression should be inside parentheses, including the keyword";

    // Semantic error messages
    public static final String REQUIRES_FIRST = "Requires clauses must be placed before all other clauses in a specification as it is a pre-condition";
    public static final String MULTIPLE_SIGNALS_ONLY = "Use a single signals_only clause to avoid confusion";
    public static final String DUPLICATE_MODIFIER = "This modifier has already been used in this specification";
    public static final String MULTIPLE_VISIBILITY_MODIFIERS = "You cannot have multiple visibility modifiers (public, protected or private)";
    public static final String MULTIPLE_SPEC_VISIBILITY_MODIFIERS = "You cannot have multiple specification visibility modifiers (spec_public or spec_protected)";
    public static final String LOOP_INVARIANT_NOT_ABOVE_LOOP = "loop_invariant / maintaining needs to be above a loop";
    public static final String HELPER_NOT_ALLOWED = "The helper modifier is only allowed when the method is private or pure";
    public static final String NOT_SPECIFIED_REDUNDANT = "This clause containing \\not_specified is redundant because you already specified it";
    public static final String STATIC_AND_INSTANCE = "You cannot use both instance and static, choose one";
    public static final String BACKSLASH_RESULT_NOT_ALLOWED = "You can only use \\result in an ensures clause";
    public static final String OLD_EXPR_NOT_ALLOWED = "You can only use an \\old() expressions in ensures and signals clauses, assert and assume statements, and in loop invariants";

    // Type error messages
    public static final String INVALID_EXPR = "Not a valid expression";
    public static final String INCORRECT_REFERENCE = "This is not a correct reference";
    public static final String ASSIGNABLE_ARRAY_ONLY = "You can only use '[*]' on arrays";
    public static final String ASSIGNABLE_CLASS_ONLY = "You can only use '.*' on classes and interfaces";
    public static final String UNASSIGNABLE = "This cannot be assigned";
    public static final String NOT_A_CLASS_NAME = "This is not a class name";
    public static final String NOT_AN_EXCEPTION_CLASS = "This is not an exception class";
    public static final String PUT_IN_THROWS_CLAUSE = "This exception (or a superclass or subclass of it) should be mentioned in the throws clause of this method";
    public static final String CLASS_REFERENCE_NOT_FOUND = "This class could not be resolved, did you forget to import it?";
    public static final String OVERRIDING_LOCAL_VAR = "You are not allowed to override local variables and parameters";
    public static final String NOT_A_TYPE_NAME = "This is not the name of a primitive type or a class";
    public static final String NO_METHOD_RESULT = "Cannot use \\result here, as this method / constructor does not return anything";
    public static final String NO_ARRAY = "This is not an array";
    public static final String NO_CLASS_INSTANCE = "This should be of type java.lang.Class, maybe you forgot to use .class or .getClass()?";
    public static final String ASSIGNABLE_VAR_IS_FINAL = "This variable is final, so cannot be assigned";

    // java expression visitor error messages
    public static final String NO_ARRAY_SO_NO_ACCESS = "Array access is not allowed as this is not an array";
    public static final String STRING_NO_END = "A String must end with \"";
    public static final String CHAR_NO_END = "A char must end with '";
    public static final String INCORRECT_SYNTAX = "Incorrect syntax";
    public static final String TYPE_UNKNOWN = "Type unknown, maybe the expression is invalid?";
    public static final String ARRAY_DIM_NO_INT = "Array dimensions should be of type int or something that can be converted to int";
    public static final String ARRAY_INITIALIZER_WRONG_TYPE = "Initializer is not the same type as the array element type";
    public static final String METHOD_UNRESOLVED = "Method could not be resolved, maybe the parameters do not correspond?";
    public static final String CONSTRUCTOR_UNRESOLVED = "Constructor could not be resolved, maybe the parameters do not correspond?";
    public static final String INCOMPATIBLE_CAST = "Incompatible type cast";
    public static final String INVARIANT_WRONG_VISIBILITY = "The (specification) visibility of the reference should be the same as the visibility of the invariant";
    public static final String FIELD_NO_MODIFIERS = "The referenced field has no modifiers, so cannot check visibility constraints";
    public static final String INVARIANT_SHOULD_BE_STATIC = "A static invariant can only see static fields";
    public static final String VARIABLE_EXPECTED = "Variable expected";
    public static final String NOT_A_CLASS = "This is not a class";
    public static final String REFERENCE_UNRESOLVED = "Reference cannot be resolved";
    public static final String METHOD_NOT_PURE = "JML expressions should be pure and this method might not be pure";
    public static final String ASSIGNMENT_NOT_PURE = "JML expressions should be pure and assignments are not pure";

    // Other error messages
    public static final String WS_BEFORE_AT_SIGN = "To be considered a JML comment, there should be no whitespace between the start of the comment (/* or //) and the @-sign";

    // holds text replacements for certain tokens
    public static final Map<String, String> internalToDisplayText = new HashMap<>();

    static {
        internalToDisplayText.put("<", "");
        internalToDisplayText.put(">", "");
        internalToDisplayText.put("LBRACKET", JMLTypes.L_SQ_BRAC.toString());
        internalToDisplayText.put("RBRACKET", JMLTypes.R_SQ_BRAC.toString());
        internalToDisplayText.put("LPARENTH", JMLTypes.L_PAREN.toString());
        internalToDisplayText.put("RPARENTH", JMLTypes.R_PAREN.toString());
    }

    /**
     * Replaces a comma-separated list of modifiers with the text "modifiers"
     *
     * @param input the string to change
     * @return the string with the replacements
     */
    public static String replaceAllModifiers(String input) {
        String regex = JMLAnnotatorUtil.ALL_MODIFIERS_REGEX + ",?";
        String output = input.replaceAll("(^| )" + regex, "").replaceAll(", (\\w+), or$", " or $1");
        return (output.contains("modifiers") ? "" : "modifier, ") + output;
    }

    public static String modifierNotAllowedHere(String modifier, CommentPosition position) {
        return "Modifier '" + modifier + "' is not allowed " + position.getPositionString();
    }

    public static String specKindNotAllowedHere(PsiElement specKind, CommentPosition position) {
        String specKindStr = "This";
        if (specKind instanceof JMLModifiers) {
            specKindStr = "Modifiers";
        } else if (specKind instanceof JMLMethodJml) {
            specKindStr = "Method specifications";
        } else if (specKind instanceof JMLInMethodSpec) {
            specKindStr = "In-method specifications";
        } else if (specKind instanceof JMLClassInvariant) {
            return "Class invariants are not allowed " + position.getPositionString()
                    + (position == CommentPosition.FIELD ? ", add a newline after the comment" : "");
        }
        return specKindStr + " are not allowed " + position.getPositionString();
    }

    public static String wrongType(@NotNull String expectedType, @Nullable PsiType actualType) {
        String start = "This must be of type " + expectedType;
        if (expectedType.equals("")) start = "This is not allowed to be of type ";
        if (actualType != null) {
            return start + ", but is " + actualType.getPresentableText();
        }
        return start + ".";
    }

    public static String wrongInstanceOf(@NotNull PsiType from, @NotNull PsiType to) {
        return "Expression of type " + from.getPresentableText() + " can never be instance of " + to.getPresentableText();
    }

    public static String wrongCast(@NotNull PsiType from, @NotNull PsiType to) {
        return "Expression of type " + from.getPresentableText() + " cannot be cast to " + to.getPresentableText();
    }

    public static String castToSubType(@NotNull PsiType from, @NotNull PsiType to) {
        return to.getPresentableText() + " is a subtype of " + from.getPresentableText() + ", so this might produce a ClassCastException";
    }

    public static String wrongUnary(@NotNull String sign, @Nullable PsiType type) {
        return "The operator '" + sign + "' is not applicable "
                + (type != null ? "to an operand of type " + type.getPresentableText() : "here");
    }

    public static String wrongPolyadic(@NotNull PsiExpression lOp, @NotNull PsiExpression rOp) {
        String result = "This operator cannot be applied to type ";
        result += lOp.getType() != null ? lOp.getType().getPresentableText() : "unknown";
        result += " and type ";
        result += rOp.getType() != null ? rOp.getType().getPresentableText() : "unknown";
        return result;
    }
}
