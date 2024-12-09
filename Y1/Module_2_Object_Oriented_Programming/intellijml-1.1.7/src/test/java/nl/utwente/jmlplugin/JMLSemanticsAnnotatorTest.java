package nl.utwente.jmlplugin;

import com.intellij.openapi.roots.LanguageLevelProjectExtension;
import com.intellij.pom.java.LanguageLevel;
import com.intellij.testFramework.fixtures.LightJavaCodeInsightFixtureTestCase;

/**
 * Tests that correct semantic errors are given
 */
public class JMLSemanticsAnnotatorTest extends LightJavaCodeInsightFixtureTestCase {


    @Override
    protected void setUp() throws Exception {
        super.setUp();
        LanguageLevelProjectExtension.getInstance(getProject()).setLanguageLevel(LanguageLevel.JDK_11);
    }

    @Override
    protected String getTestDataPath() {
        return "src/test/semanticsAnnotatorTestData";
    }


    public void testSpecKindNotAllowedHere() {
        myFixture.configureByFile("SpecKindNotAllowedHere.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testModifierBeforeClause() {
        myFixture.configureByFile("ModifierBeforeClause.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testMultipleSignalsOnly() {
        myFixture.configureByFile("MultipleSignalsOnly.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testModifierKindNotAllowedHere() {
        myFixture.configureByFile("ModifierKindNotAllowedHere.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testStaticAndInstanceModifiers() {
        myFixture.configureByFile("StaticAndInstanceModifiers.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testHelperModifierAllowed() {
        myFixture.configureByFile("HelperModifierAllowed.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testMultipleVisibilityModifiers() {
        myFixture.configureByFile("MultipleVisibilityModifiers.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testMultipleSpecVisibilityModifiers() {
        myFixture.configureByFile("MultipleSpecVisibilityModifiers.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testDuplicateModifiers() {
        myFixture.configureByFile("DuplicateModifiers.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testLoopInvariantNotAboveLoop() {
        myFixture.configureByFile("LoopInvariantNotAboveLoop.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testRedundantNotSpecified() {
        myFixture.configureByFile("RedundantNotSpecified.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testBackslashResultAllowed() {
        myFixture.configureByFile("BackslashResultAllowed.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testOldExpressionAllowed() {
        myFixture.configureByFile("OldExpressionAllowed.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testMultipleDuplicateVisibilityModifiers() {
        myFixture.configureByFile("MultipleDuplicateVisibilityModifiers.java");
        myFixture.checkHighlighting(true, false, true, false);
    }


}
