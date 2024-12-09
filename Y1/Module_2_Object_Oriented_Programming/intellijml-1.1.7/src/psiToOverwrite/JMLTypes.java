package nl.utwente.jmlplugin.psi;

import com.intellij.psi.tree.IElementType;
import com.intellij.psi.PsiElement;
import com.intellij.lang.ASTNode;
import nl.utwente.jmlplugin.psi.impl.*;

public interface JMLTypes {
    // Don't you dare overwrite this with the generated version,
    // the strings here are also displayed in syntax error messages to the user

    IElementType ASSERT_STATEMENT = new JMLElementType("assert statement");
    IElementType ASSIGNABLE_CLAUSE = new JMLElementType("assignable clause");
    IElementType ASSUME_STATEMENT = new JMLElementType("assume statement");
    IElementType CLASS_INVARIANT = new JMLElementType("class invariant");
    IElementType ENSURES_CLAUSE = new JMLElementType("ensures clause");
    IElementType IN_METHOD_SPEC = new JMLElementType("in-method specification");
    IElementType JAVA_EXPR = new JMLElementType("expression");
    IElementType JML_SPECIFICATION = new JMLElementType("JML specification");
    IElementType LOOP_INVARIANT = new JMLElementType("loop invariant");
    IElementType METHOD_JML = new JMLElementType("method specification");
    IElementType METHOD_SPEC = new JMLElementType("method specification clauses");
    IElementType MODIFIERS = new JMLElementType("modifiers");
    IElementType REFERENCE_TYPE = new JMLElementType("reference to an exception class");
    IElementType REQUIRES_CLAUSE = new JMLElementType("requires clause");
    IElementType SIGNALS_CLAUSE = new JMLElementType("signals clause");
    IElementType SIGNALS_ONLY_CLAUSE = new JMLElementType("signals_only clause");
    IElementType SPEC_BODY = new JMLElementType("specification clause");
    IElementType STORE_REF = new JMLElementType("reference to a field, all fields in a class (with .*), or Objects in an array (with [*])");
    IElementType STORE_REF_KEYWORD = new JMLElementType("\\nothing, \\everything or \\not_specified");
    // Added manually
    IElementType QUANTIFIED_EXPR = new JMLElementType("quantified expression");
    IElementType Q_VAR_DECL = new JMLElementType("variable declaration");
    IElementType TYPE_NAME = new JMLElementType("type");
    IElementType Q_VAR_DECL_IDENTIFIER = new JMLElementType("variable name");
    IElementType Q_PREDICATE = new JMLElementType("range condition");
    IElementType Q_SPEC_EXPR = new JMLElementType("expression");
    IElementType OLD_EXPR = new JMLElementType("\\old() expression");
    IElementType TYPE_OF_EXPR = new JMLElementType("\\typeof() expression");
    IElementType ELEM_TYPE_EXPR = new JMLElementType("\\elemtype() expression");
    IElementType TYPE_EXPR = new JMLElementType("\\type() expression");
    IElementType NON_NULL_ELEMENTS_EXPR = new JMLElementType("\\nonnullelements() expression");
    IElementType INNER_JAVA_EXPR = new JMLElementType("expression");

    IElementType ALSO = new JMLTokenType("also");
    IElementType ASSERT = new JMLTokenType("assert");
    IElementType ASSIGNABLE = new JMLTokenType("assignable");
    IElementType ASSUME = new JMLTokenType("assume");
    IElementType AT_SIGN = new JMLTokenType("at-sign");
    IElementType COLON = new JMLTokenType("colon");
    IElementType COMMA = new JMLTokenType("comma");
    IElementType DOT = new JMLTokenType("period");
    IElementType ENSURES = new JMLTokenType("ensures");
    IElementType EVERYTHING = new JMLTokenType("\\everything");
    IElementType HELPER = new JMLTokenType("helper");
    IElementType IDENT = new JMLTokenType("identifier");
    IElementType INFORMAL_DESCRIPTION = new JMLTokenType("informal description");
    IElementType INSTANCE = new JMLTokenType("instance");
    IElementType INTO = new JMLTokenType("\\into");
    IElementType INVARIANT = new JMLTokenType("invariant");
    IElementType LOOPINVARIANT = new JMLTokenType("loop_invariant");
    IElementType L_PAREN = new JMLTokenType("left parenthesis");
    IElementType L_SQ_BRAC = new JMLTokenType("left bracket");
    IElementType MAINTAINING = new JMLTokenType("maintaining");
    IElementType MODIFIABLE = new JMLTokenType("modifiable");
    IElementType MODIFIES = new JMLTokenType("modifies");
    IElementType NOTHING = new JMLTokenType("\\nothing");
    IElementType NOT_SPECIFIED = new JMLTokenType("\\not_specified");
    IElementType NULLABLE = new JMLTokenType("nullable");
    IElementType POST = new JMLTokenType("post");
    IElementType PRE = new JMLTokenType("pre");
    IElementType PRIVATE = new JMLTokenType("private");
    IElementType PROTECTED = new JMLTokenType("protected");
    IElementType PUBLIC = new JMLTokenType("public");
    IElementType PURE = new JMLTokenType("pure");
    IElementType REQUIRES = new JMLTokenType("requires");
    IElementType REST = new JMLTokenType("REST");
    IElementType R_PAREN = new JMLTokenType("right parenthesis");
    IElementType R_SQ_BRAC = new JMLTokenType("right bracket");
    IElementType SEMICOLON = new JMLTokenType("semicolon");
    IElementType SIGNALS = new JMLTokenType("signals");
    IElementType SIGNALS_ONLY = new JMLTokenType("signals_only");
    IElementType SPEC_PROTECTED = new JMLTokenType("spec_protected");
    IElementType SPEC_PUBLIC = new JMLTokenType("spec_public");
    IElementType STAR = new JMLTokenType("asterisk");
    IElementType STATIC = new JMLTokenType("static");
    IElementType SUPER = new JMLTokenType("super");
    IElementType THIS = new JMLTokenType("this");

    // Added manually
    IElementType JAVA_EXPR_TOKEN = new JMLTokenType("JAVA_EXPR_TOKEN");
    IElementType RESULT = new JMLTokenType("\\result");
    IElementType OLD = new JMLTokenType("\\old");
    IElementType FORALL = new JMLTokenType("\\forall");
    IElementType EXISTS = new JMLTokenType("\\exists");
    IElementType MAX = new JMLTokenType("\\max");
    IElementType MIN = new JMLTokenType("\\min");
    IElementType NUM_OF = new JMLTokenType("\\num_of");
    IElementType PRODUCT = new JMLTokenType("\\product");
    IElementType SUM = new JMLTokenType("\\sum");
    IElementType TYPE_OF = new JMLElementType("\\typeof");
    IElementType ELEM_TYPE = new JMLElementType("\\elemtype");
    IElementType TYPE = new JMLElementType("\\type");
    IElementType TYPE_CAPS = new JMLElementType("\\TYPE");
    IElementType NON_NULL_ELEMENTS = new JMLElementType("\\nonnullelements");
    IElementType LOGICAL_IMPL = new JMLElementType("==>");
    IElementType LOGICAL_EQ = new JMLElementType("<==>");
    IElementType LOGICAL_IMPL_REV = new JMLElementType("<==");
    IElementType LOGICAL_NOT_EQ = new JMLElementType("<=!=>");

    class Factory {
        public static PsiElement createElement(ASTNode node) {
            IElementType type = node.getElementType();
            if (type == ASSERT_STATEMENT) {
                return new JMLAssertStatementImpl(node);
            } else if (type == ASSIGNABLE_CLAUSE) {
                return new JMLAssignableClauseImpl(node);
            } else if (type == ASSUME_STATEMENT) {
                return new JMLAssumeStatementImpl(node);
            } else if (type == CLASS_INVARIANT) {
                return new JMLClassInvariantImpl(node);
            } else if (type == ENSURES_CLAUSE) {
                return new JMLEnsuresClauseImpl(node);
            } else if (type == IN_METHOD_SPEC) {
                return new JMLInMethodSpecImpl(node);
            } else if (type == JAVA_EXPR) {
                return new JMLJavaExprImpl(node);
            } else if (type == JML_SPECIFICATION) {
                return new JMLJmlSpecificationImpl(node);
            } else if (type == LOOP_INVARIANT) {
                return new JMLLoopInvariantImpl(node);
            } else if (type == METHOD_JML) {
                return new JMLMethodJmlImpl(node);
            } else if (type == METHOD_SPEC) {
                return new JMLMethodSpecImpl(node);
            } else if (type == MODIFIERS) {
                return new JMLModifiersImpl(node);
            } else if (type == REFERENCE_TYPE) {
                return new JMLReferenceTypeImpl(node);
            } else if (type == REQUIRES_CLAUSE) {
                return new JMLRequiresClauseImpl(node);
            } else if (type == SIGNALS_CLAUSE) {
                return new JMLSignalsClauseImpl(node);
            } else if (type == SIGNALS_ONLY_CLAUSE) {
                return new JMLSignalsOnlyClauseImpl(node);
            } else if (type == SPEC_BODY) {
                return new JMLSpecBodyImpl(node);
            } else if (type == STORE_REF) {
                return new JMLStoreRefImpl(node);
            } else if (type == STORE_REF_KEYWORD) {
                return new JMLStoreRefKeywordImpl(node);
            }
            // Added manually
            else if (type == QUANTIFIED_EXPR) {
                return new JMLQuantifiedExpr(node);
            } else if (type == Q_VAR_DECL) {
                return new JMLQVarDecl(node);
            } else if (type == TYPE_NAME) {
                return new JMLTypeName(node);
            } else if (type == Q_VAR_DECL_IDENTIFIER) {
                return new JMLQVarDeclIdentifier(node);
            } else if (type == Q_PREDICATE) {
                return new JMLQPredicate(node);
            } else if (type == Q_SPEC_EXPR) {
                return new JMLQSpecExpr(node);
            } else if (type == OLD_EXPR) {
                return new JMLOldExpr(node);
            } else if (type == TYPE_OF_EXPR) {
                return new JMLTypeOfExpr(node);
            } else if (type == ELEM_TYPE_EXPR) {
                return new JMLElemTypeExpr(node);
            } else if (type == TYPE_EXPR) {
                return new JMLTypeExpr(node);
            } else if (type == NON_NULL_ELEMENTS_EXPR) {
                return new JMLNonNullElementsExpr(node);
            } else if (type == INNER_JAVA_EXPR) {
                return new JMLInnerJavaExpr(node);
            }
            throw new AssertionError("Unknown element type: " + type);
        }
    }
}
