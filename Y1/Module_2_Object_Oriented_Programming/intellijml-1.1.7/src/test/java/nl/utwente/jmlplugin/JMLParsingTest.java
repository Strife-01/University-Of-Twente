package nl.utwente.jmlplugin;

import com.intellij.testFramework.ParsingTestCase;

/**
 * Tests that the parsers generate correct parse trees and error elements at the correct places
 */
public class JMLParsingTest extends ParsingTestCase {

    public JMLParsingTest() {
        super("", "jml", true, new JMLParserDefinition());
    }

    @Override
    protected String getTestDataPath() {
        return "src/test/parserTestData";
    }

    @Override
    protected boolean skipSpaces() {
        return true;
    }

    @Override
    protected boolean includeRanges() {
        return true;
    }

    @Override
    protected boolean allTreesInSingleFile() {
        return true;
    }

    public void testAllCorrectMethodSpecCases() {
        doTest(true, true);
    }

    public void testCorrectAssert() {
        doTest(true, true);
    }

    public void testCorrectAssume() {
        doTest(true, true);
    }

    public void testCorrectClassInvariant() {
        doTest(true, true);
    }

    public void testCorrectLoopInvariant() {
        doTest(true, true);
    }

    public void testCorrectMaintaining() {
        doTest(true, true);
    }

    public void testCorrectOrderRequiresEnsures() {
        doTest(true, true);
    }

    public void testCorrectQuantifiers() {
        doTest(true, true);
    }

    public void testCorrectWhiteSpace() {
        doTest(true, true);
    }

    public void testEmptyJavaExpr() {
        doTest(true, false);
    }

    public void testModifierExpected() {
        doTest(true, false);
    }

    public void testModifiersBeforeSpecClause() {
        doTest(true, false);
    }

    public void testMultipleAtSigns() {
        doTest(true, true);
    }

    public void testNoWhitespaceAfterKeyword() {
        doTest(true, false);
    }

    public void testQuantifierStartKeywordOnly() {
        doTest(true, false);
    }

    public void testQuantifierTillPredicate() {
        doTest(true, false);
    }

    public void testQuantifierTillVarDecl() {
        doTest(true, false);
    }

    public void testQuantifierWithoutParens() {
        doTest(true, false);
    }

    public void testRedundantSemicolons() {
        doTest(true, true);
    }

    public void testSemicolonForgotten() {
        doTest(true, false);
    }

    public void testSignalsOnlyWithParentheses() {
        doTest(true, false);
    }

    public void testSignalsWithoutParentheses() {
        doTest(true, false);
    }

    public void testUnfinishedJavaExpr() {
        doTest(true, false);
    }

    public void testWrongOrderRequiresEnsures() {
        doTest(true, false);
    }

    public void testWrongOrderRequiresEnsuresWithAlso() {
        doTest(true, true);
    }

    public void testBackslashOldWithoutContents() {
        doTest(true, false);
    }

    public void testBackslashOldWithoutParentheses() {
        doTest(true, false);
    }

    public void testCorrectBackslashKeywords() {
        doTest(true, true);
    }

    public void testMissingParentheses() {
        doTest(true, false);
    }

}
