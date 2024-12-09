package nl.utwente.jmlplugin;

import com.intellij.openapi.module.Module;
import com.intellij.openapi.roots.LanguageLevelProjectExtension;
import com.intellij.pom.java.LanguageLevel;
import com.intellij.testFramework.builders.JavaModuleFixtureBuilder;
import com.intellij.testFramework.fixtures.JavaCodeInsightFixtureTestCase;

/**
 * Tests that all the type checking is done correctly so that the error messages are shown at the
 * correct spot and that they are only shown when there is an actual type error
 */
public class JMLTypeAnnotatorTest extends JavaCodeInsightFixtureTestCase {

    @Override
    protected void setUp() throws Exception {
        super.setUp();
        LanguageLevelProjectExtension.getInstance(getProject()).setLanguageLevel(LanguageLevel.JDK_1_8);
    }

    @Override
    protected void tuneFixture(JavaModuleFixtureBuilder<?> moduleBuilder) throws Exception {
        super.tuneFixture(moduleBuilder);
        moduleBuilder.addMavenLibrary(new JavaModuleFixtureBuilder.MavenLib("org.jetbrains:annotations:24.1.0"));
    }

    @Override
    protected String getTestDataPath() {
        return "src/test/typeAnnotatorTestData";
    }

    public void testAssignableVars() {
        myFixture.configureByFile("AssignableVars.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testSignalsExceptionReferences() {
        myFixture.configureByFile("SignalsExceptionReferences.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testInvariantVisibility() {
        myFixture.configureByFile("InvariantVisibility.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testInvariantVisibilityMethods() {
        myFixture.configureByFile("InvariantVisibilityMethods.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testInvariantStaticAndInstance() {
        myFixture.configureByFile("InvariantStaticAndInstance.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testBackslashOld() {
        myFixture.configureByFile("BackslashOld.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testBackslashResult() {
        myFixture.configureByFile("BackslashResult.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testBackslashTypeFunctions() {
        myFixture.configureByFile("BackslashTypeFunctions.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testJMLOperators() {
        myFixture.configureByFile("JMLOperators.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testQuantifiedExpressions() {
        myFixture.configureByFile("QuantifiedExpressions.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testJavaArrays() {
        myFixture.configureByFile("JavaArrays.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testJavaAssignments() {
        myFixture.configureByFile("JavaAssignments.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testJavaBooleanExpressions() {
        myFixture.configureByFile("JavaBooleanExpressions.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testCallExpressions() {
        myFixture.configureByFile("JavaCallExpressions.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testJavaInstanceofAndCasting() {
        myFixture.configureByFile("JavaInstanceofAndCasting.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testJavaLiterals() {
        myFixture.configureByFile("JavaLiterals.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testNewExpressions() {
        myFixture.configureByFile("JavaNewExpressions.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testParenthesizedExpressions() {
        myFixture.configureByFile("JavaParenthesizedExpressions.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testJavaReferences() {
        myFixture.configureByFile("JavaReferences.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testJavaUnaryExpressions() {
        myFixture.configureByFile("JavaUnaryExpressions.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testPurenessOfCalls() {
        myFixture.configureByFile("PurenessOfCalls.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testSpecVisibilityAcrossClasses() {
        myFixture.configureByFile("SpecVisibilityAcrossClasses.java");
        myFixture.checkHighlighting(true, false, true, false);
    }


}
