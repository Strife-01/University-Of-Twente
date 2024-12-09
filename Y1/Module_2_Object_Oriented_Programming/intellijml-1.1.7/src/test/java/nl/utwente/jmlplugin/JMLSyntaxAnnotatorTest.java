package nl.utwente.jmlplugin;

import com.intellij.openapi.roots.LanguageLevelProjectExtension;
import com.intellij.pom.java.LanguageLevel;
import com.intellij.testFramework.fixtures.JavaCodeInsightFixtureTestCase;
import com.intellij.testFramework.fixtures.LightJavaCodeInsightFixtureTestCase;

/**
 * Tests that correct syntax errors are given
 */
public class JMLSyntaxAnnotatorTest extends JavaCodeInsightFixtureTestCase {

    @Override
    protected void setUp() throws Exception {
        super.setUp();
        LanguageLevelProjectExtension.getInstance(getProject()).setLanguageLevel(LanguageLevel.JDK_11);
    }

    @Override
    protected String getTestDataPath() {
        return "src/test/syntaxAnnotatorTestData";
    }

    public void testWhitespaceAroundAt() {
        myFixture.configureByFile("WhitespaceAroundAt.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testRequiresAfterEnsures() {
        myFixture.configureByFile("RequiresAfterEnsures.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testModifierBeforeClause() {
        myFixture.configureByFile("ModifierBeforeClause.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testSignalsWithoutParens() {
        myFixture.configureByFile("SignalsWithoutParens.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testSquareBraceButNotStar() {
        myFixture.configureByFile("SquareBraceButNotStar.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testSignalsOnlySyntaxError() {
        myFixture.configureByFile("SignalsOnlySyntaxError.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testQuantifierSyntax() {
        myFixture.configureByFile("QuantifierSyntax.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testModifierExpected() {
        myFixture.configureByFile("ModifierExpected.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testClauseWithoutExpression() {
        myFixture.configureByFile("ClauseWithoutExpression.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testMissingSemicolon() {
        myFixture.configureByFile("MissingSemicolon.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testMiscSyntax() {
        myFixture.configureByFile("MiscSyntax.java");
        myFixture.checkHighlighting(true, false, true, false);
    }


}
